-------------------------- MODULE disclosure --------------------------
(***************************************************************************)
(* Transcript disclosure, as a protocol — the temporal projection of the    *)
(* model in ../../Keycard/Transcript.lean.                                  *)
(*                                                                          *)
(* The Lean arc proves the pure-policy properties for all inputs: what a    *)
(* policy may permit, given a decision, a session and an upload. It cannot   *)
(* see the gap this module exists for, because that gap is temporal.         *)
(*                                                                          *)
(* THE GAP. `path share` does not decide and upload in one step. It runs     *)
(* `preflight_auth`, then derives the graph, then uploads — three phases,    *)
(* with real time in between (the derive is the expensive one). So the       *)
(* decision that authorises the upload is read at one instant and acted on   *)
(* at a later one. Between them the owner can withdraw consent and a         *)
(* credential can be revoked. Bytes already sent do not come back.           *)
(*                                                                          *)
(* Every check-then-act is therefore split across TWO actions, with a yield  *)
(* point between them, so TLC explores the interleavings a real session      *)
(* would hit.                                                                *)
(*                                                                          *)
(*   Atomic = FALSE           -> the upload trusts the stale preflight read. *)
(*   Atomic = TRUE            -> the upload re-evaluates at commit.          *)
(*   AllowAnonFallback = TRUE -> a credential failure downgrades to the      *)
(*                               ANONYMOUS endpoint instead of refusing.     *)
(*                                                                          *)
(* AllowAnonFallback is not invented. It is `preflight_auth`'s measured      *)
(* behaviour (empathic/toolpath@68aacef, cmd_pathbase.rs:263): with no       *)
(* auth-requiring flag, absent or rejected credentials yield AuthMode::Anon  *)
(* and the upload proceeds. It is TRUE exactly when `needs_auth` is false,   *)
(* i.e. when none of --repo / --public / --name is passed.                   *)
(*                                                                          *)
(* THE POINT OF THE THREE CONFIGS: the two faults are INDEPENDENT. Making    *)
(* the check atomic does not close the anonymous fallback, and forbidding    *)
(* the fallback does not close the TOCTOU. disclosure-anon.cfg exists to     *)
(* exhibit exactly that — it is Atomic = TRUE and still breaks.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Sessions,           \* set of session ids, e.g. {s1, s2}
          Atomic,             \* TRUE = re-evaluate consent+creds at commit
          AllowAnonFallback   \* TRUE = credential failure downgrades to anonymous

VARIABLES consent,        \* BOOLEAN: the owner's standing disclosure decision
          authed,         \* BOOLEAN: do the session's credentials validate
          pc,             \* [Sessions -> {"idle","checked","done"}]
          gConsent,       \* [Sessions -> BOOLEAN]: consent as read at preflight
          gAuthed,        \* [Sessions -> BOOLEAN]: creds as read at preflight
          published,      \* SUBSET Sessions: uploaded under an account we own
          anonPublished,  \* SUBSET Sessions: uploaded anonymously — UNRETRACTABLE
          violated        \* BOOLEAN: an upload happened while consent was FALSE

vars == <<consent, authed, pc, gConsent, gAuthed, published, anonPublished, violated>>

TypeOK ==
  /\ consent       \in BOOLEAN
  /\ authed        \in BOOLEAN
  /\ pc            \in [Sessions -> {"idle", "checked", "done"}]
  /\ gConsent      \in [Sessions -> BOOLEAN]
  /\ gAuthed       \in [Sessions -> BOOLEAN]
  /\ published     \subseteq Sessions
  /\ anonPublished \subseteq Sessions
  /\ violated      \in BOOLEAN

(* Start permitted and authenticated. Starting from the permissive state is  *)
(* deliberate: it means every counterexample TLC finds is a case where       *)
(* something that WAS allowed became disallowed and the upload went anyway,  *)
(* which is the failure being hunted. Starting from refusal would make the   *)
(* invariants hold trivially.                                                *)
Init ==
  /\ consent       = TRUE
  /\ authed        = TRUE
  /\ pc            = [s \in Sessions |-> "idle"]
  /\ gConsent      = [s \in Sessions |-> FALSE]
  /\ gAuthed       = [s \in Sessions |-> FALSE]
  /\ published     = {}
  /\ anonPublished = {}
  /\ violated      = FALSE

\* PREFLIGHT: read consent and credentials. Mutates nothing else — this is
\* the race window, and in the real CLI it is as wide as the derive step.
Check(s) ==
  /\ pc[s] = "idle"
  /\ gConsent' = [gConsent EXCEPT ![s] = consent]
  /\ gAuthed'  = [gAuthed  EXCEPT ![s] = authed]
  /\ pc'       = [pc EXCEPT ![s] = "checked"]
  /\ UNCHANGED <<consent, authed, published, anonPublished, violated>>

\* What the upload believes, which is the stale read unless Atomic.
SeesConsent(s) == IF Atomic THEN consent ELSE gConsent[s]
SeesAuthed(s)  == IF Atomic THEN authed  ELSE gAuthed[s]

\* COMMIT the upload. Note `violated` is set against the REAL consent at this
\* instant, not against what the session believed — the whole question is
\* whether belief and truth can diverge here.
Upload(s) ==
  /\ pc[s] = "checked"
  /\ pc' = [pc EXCEPT ![s] = "done"]
  /\ IF ~SeesConsent(s)
       THEN \* policy refused — nothing leaves
            /\ UNCHANGED <<published, anonPublished, violated>>
       ELSE IF SeesAuthed(s)
         THEN /\ published'      = published \cup {s}
              /\ violated'       = (violated \/ ~consent)
              /\ UNCHANGED anonPublished
         ELSE IF AllowAnonFallback
           THEN \* preflight_auth's downgrade: it uploads, unretractably
                /\ anonPublished' = anonPublished \cup {s}
                /\ violated'      = (violated \/ ~consent)
                /\ UNCHANGED published
           ELSE \* needs_auth set: the error propagates, nothing leaves
                /\ UNCHANGED <<published, anonPublished, violated>>
  /\ UNCHANGED <<consent, authed, gConsent, gAuthed>>

\* The owner withdraws the standing decision. One-way, so the state space
\* stays finite.
WithdrawConsent ==
  /\ consent
  /\ consent' = FALSE
  /\ UNCHANGED <<authed, pc, gConsent, gAuthed, published, anonPublished, violated>>

\* A credential is revoked or expires mid-flight. Also one-way.
RevokeCreds ==
  /\ authed
  /\ authed' = FALSE
  /\ UNCHANGED <<consent, pc, gConsent, gAuthed, published, anonPublished, violated>>

SessionStep == \E s \in Sessions : Check(s) \/ Upload(s)

AllDone == \A s \in Sessions : pc[s] = "done"

\* Explicit stutter once every session has finished. This system genuinely
\* terminates, and without this TLC reports the terminal state as a deadlock.
\* Stuttering here rather than setting CHECK_DEADLOCK FALSE keeps deadlock
\* checking ON, so a genuine stall in a NON-final state would still be caught.
Terminating == AllDone /\ UNCHANGED vars

Next == SessionStep \/ WithdrawConsent \/ RevokeCreds \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(SessionStep)

(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

\* Nothing was uploaded at an instant when the owner's decision said no.
\* This is the temporal half of Lean's `DecisionGrounded` — that property
\* quantifies over a decision record, this one over the moment of use.
NoUnconsentedDisclosure == violated = FALSE

\* Nothing was uploaded anonymously. This is exactly the retractability
\* property: an anonymous upload has no owner, so no account exists from
\* which to delete it. `anonPublished` is the set of things that can never
\* be taken back — the invariant is that it stays empty.
\* Lean's counterpart is `anon_refused_under_any_decision`.
NoAnonUpload == anonPublished = {}

(***************************************************************************)
(* LIVENESS — checked only in the safe config.                             *)
(* Fail-CLOSED must not mean fail-STUCK: refusing is a decision the session *)
(* reaches and reports, not a hang. Every session finishes.                 *)
(***************************************************************************)
Termination == <>AllDone

=============================================================================
