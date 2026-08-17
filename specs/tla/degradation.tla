-------------------------- MODULE degradation --------------------------
(***************************************************************************)
(* Degrading authority, as a protocol — the temporal projection of the      *)
(* model in ../../Keycard/Authority.lean.                                   *)
(*                                                                          *)
(* THE SENTENCE THIS MODELS.                                                *)
(*                                                                          *)
(*   GITHUB_TOKEN: ${{ secrets.BOOTSTRAP_TOKEN || secrets.GITHUB_TOKEN }}   *)
(*                                                                          *)
(* Four workflows in bounded-systems/content-catalog read the credential    *)
(* that way (bootstrap.yml:50, aggregate.yml:48, enrich.yml:40,             *)
(* seed.yml:35 — content-catalog#10). A 2026-08-16 credential audit revoked *)
(* the PAT behind secrets.BOOTSTRAP_TOKEN. The `||` did not fail; it        *)
(* resolved to the next term, which is repo-scoped and read-only by org     *)
(* default. Revocation substituted a weaker principal and reported success. *)
(*                                                                          *)
(* WHAT TLC SEES THAT LEAN CANNOT. The Lean arc proves the pure properties  *)
(* for all inputs: given a revocation record, a named authority, a fallback *)
(* and an operation, what may a runner do. It cannot see that the run is    *)
(* not one step. The credential is SELECTED when the expression is          *)
(* evaluated and USED over the minutes that follow, one target at a time.   *)
(* So revocation has two distinct places to land — before selection, where  *)
(* it causes substitution, and mid-run, where it truncates a run already    *)
(* under way. Both end green. Only the second is invisible to the Lean      *)
(* model, and it is why the check-then-act is split across `Select` and     *)
(* `Visit` with a yield point between, exactly as disclosure.tla splits     *)
(* preflight from upload.                                                   *)
(*                                                                          *)
(*   AllowFallback  = TRUE  -> `||` substitutes the weaker principal.       *)
(*   GreenOnPartial = TRUE  -> the run reports success on whatever it       *)
(*                             reached, rather than on having reached all.  *)
(*                                                                          *)
(* THE POINT OF THE FOUR CONFIGS: the two faults are INDEPENDENT, and the   *)
(* two isolating configs exhibit that in both directions. Stop substituting *)
(* and a truncated run still ships green; stop greening partials and        *)
(* effects still land under a principal the policy never named. This is the *)
(* temporal restatement of the Lean independence pair —                     *)
(* runnerBestEffort and runnerSufficientFallback in Degradation.lean        *)
(* violate disjoint sets of properties for the same reason.                 *)
(*                                                                          *)
(* ONE RUN, NOT TWO. disclosure.tla models two sessions because its fault   *)
(* is a race between a session and the owner. This fault is a race between  *)
(* a run and the CREDENTIAL LIFECYCLE, which a second run does not          *)
(* illuminate — the four content-catalog workflows degraded independently   *)
(* and identically, and did not interact. One run keeps the state space     *)
(* small enough to read the counterexample traces by eye.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Repos,           \* the operation's targets — the org's repos
          FallbackCovers,  \* the capability set of the substitute principal
          AllowFallback,   \* TRUE = `A || B` substitutes on revocation
          GreenOnPartial   \* TRUE = report success on whatever was reached

(* The fallback is STRICTLY WEAKER — that is the whole premise, so it is    *)
(* checked rather than assumed in prose. The Lean counterpart is            *)
(* fxGithubToken_strictly_weaker, closed by kernel decide. A config that    *)
(* set FallbackCovers = Repos would be modelling a different incident, and  *)
(* TLC refuses it here rather than quietly passing.                         *)
ASSUME /\ FallbackCovers \subseteq Repos
       /\ FallbackCovers # Repos

VARIABLES namedLive,      \* BOOLEAN: is the policy-named credential live
          acting,         \* which principal this run resolved to
          pc,             \* "idle" | "selected" | "done"
          visited,        \* SUBSET Repos: targets the run actually effected
          report,         \* "pending" | "success" | "failure" — what the caller sees
          undernamed,     \* BOOLEAN: an effect landed under an unnamed principal
          silentPartial   \* BOOLEAN: success was reported over an incomplete run

vars == <<namedLive, acting, pc, visited, report, undernamed, silentPartial>>

TypeOK ==
  /\ namedLive     \in BOOLEAN
  /\ acting        \in {"unset", "named", "fallback", "none"}
  /\ pc            \in {"idle", "selected", "done"}
  /\ visited       \subseteq Repos
  /\ report        \in {"pending", "success", "failure"}
  /\ undernamed    \in BOOLEAN
  /\ silentPartial \in BOOLEAN

(* Start live and unselected. Starting from the live state is deliberate,   *)
(* for disclosure.tla's reason: every counterexample TLC finds is then a    *)
(* case where authority that WAS held was withdrawn and the work proceeded  *)
(* anyway, which is the failure being hunted. Starting revoked would make   *)
(* the invariants hold for uninteresting reasons.                           *)
Init ==
  /\ namedLive     = TRUE
  /\ acting        = "unset"
  /\ pc            = "idle"
  /\ visited       = {}
  /\ report        = "pending"
  /\ undernamed    = FALSE
  /\ silentPartial = FALSE

\* The capability lattice, as scope sets ordered by inclusion. This is the
\* same order as Authority.weakerThan in the Lean model: grant-set inclusion.
Scope(p) == CASE p = "named"    -> Repos
              [] p = "fallback" -> FallbackCovers
              [] OTHER          -> {}

\* The named credential can be revoked; secrets.GITHUB_TOKEN cannot — nobody
\* put it there and nobody can take it away, which is exactly what makes it
\* such a convenient second term.
Usable(p) == IF p = "named" THEN namedLive ELSE p = "fallback"

\* SELECT: evaluate `${{ A || B }}`. This is one instant, and everything
\* after it runs on the answer.
Select ==
  /\ pc = "idle"
  /\ acting' = IF namedLive       THEN "named"
               ELSE IF AllowFallback THEN "fallback"
               ELSE "none"
  /\ pc' = "selected"
  /\ UNCHANGED <<namedLive, visited, report, undernamed, silentPartial>>

CanVisit(r) ==
  /\ pc = "selected"
  /\ r \notin visited
  /\ Usable(acting)
  /\ r \in Scope(acting)

\* VISIT: effect the operation on one target. `undernamed` is set against the
\* principal actually acting, not against what the run believed it was — the
\* whole question is whether those two can differ without anyone noticing.
Visit(r) ==
  /\ CanVisit(r)
  /\ visited' = visited \cup {r}
  /\ undernamed' = (undernamed \/ (acting # "named"))
  /\ UNCHANGED <<namedLive, acting, pc, report, silentPartial>>

\* What the caller is told. Single source of truth so the invariant below
\* cannot drift from the reporting rule it is about.
FinalReport == IF (visited = Repos) \/ GreenOnPartial THEN "success" ELSE "failure"

\* FINISH: the run ends when nothing further is reachable — either because
\* every target was effected, or because authority ran out partway.
Finish ==
  /\ pc = "selected"
  /\ \A r \in Repos : ~CanVisit(r)
  /\ pc' = "done"
  /\ report' = FinalReport
  /\ silentPartial' = (silentPartial \/ (FinalReport = "success" /\ visited # Repos))
  /\ UNCHANGED <<namedLive, acting, visited, undernamed>>

\* The credential audit. One-way, so the state space stays finite, and
\* unguarded by `pc` so it can land before selection (substitution) or in the
\* middle of the run (truncation).
Revoke ==
  /\ namedLive
  /\ namedLive' = FALSE
  /\ UNCHANGED <<acting, pc, visited, report, undernamed, silentPartial>>

RunStep == Select \/ (\E r \in Repos : Visit(r)) \/ Finish

\* Explicit stutter at the terminal state. This system genuinely terminates,
\* and without this TLC reports the terminal state as a deadlock. Stuttering
\* here rather than setting CHECK_DEADLOCK FALSE keeps deadlock checking ON,
\* so a genuine stall in a NON-final state would still be caught — the same
\* choice disclosure.tla makes, for the same reason.
Terminating == pc = "done" /\ UNCHANGED vars

Next == RunStep \/ Revoke \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(RunStep)

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

\* No effect ever landed under a principal the policy did not name. The
\* temporal half of Lean's `ActsAsNamed`: that property quantifies over an
\* outcome, this one over every instant at which an effect occurred.
NoUndernamedEffect == undernamed = FALSE

\* Success was never reported over an incomplete run. The temporal half of
\* Lean's `Faithful`, and the invariant that would have caught the real
\* consequence: the catalog is committed AND SLSA-attested, so a run that
\* silently narrowed shipped a partial artifact with full provenance.
NoSilentPartial == silentPartial = FALSE

(***************************************************************************)
(* LIVENESS — checked only in the safe config.                             *)
(* Fail-CLOSED must not mean fail-STUCK: refusing is an outcome the run     *)
(* reaches and reports, not a hang. This matters more here than in the      *)
(* disclosure arc, because the fix being modelled is "refuse instead of     *)
(* substituting", and a fix that deadlocks the lane would not survive       *)
(* contact with anyone's CI.                                               *)
(***************************************************************************)
Termination == <>(pc = "done")

=============================================================================
