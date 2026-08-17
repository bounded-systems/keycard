import Keycard.Authority
/-!
# Degrading authority: the theorems

Four properties, each matching a way an operation can proceed after the
authority it was supposed to run under stopped existing.

## The sentence this arc is about

> `GITHUB_TOKEN: ${{ secrets.BOOTSTRAP_TOKEN || secrets.GITHUB_TOKEN }}`

Four workflows in `bounded-systems/content-catalog` read the credential that
way (`bootstrap.yml:50`, `aggregate.yml:48`, `enrich.yml:40`, `seed.yml:35`;
filed as `bounded-systems/content-catalog#10`). A 2026-08-16 credential audit
revoked the PAT behind `secrets.BOOTSTRAP_TOKEN`. The `||` did not fail — it
resolved to the next term. Revocation therefore did not close the door; it
**substituted a weaker principal and reported success**.

Those workflows were repaired the same day (`content-catalog#11` removed the
fallback; `content-catalog#13` replaced the credential with brokered
per-workflow OIDC mints), so the fixtures below cite a **closed incident**.
That is the `Signing.lean` discipline, not a weakening of it: a fixture is
drawn from what happened so the model can be checked against it, and none of
these theorems observed the live system or contributed to its repair.

## How these theorems avoid being vacuous

The discipline is `Signing.lean`'s, unchanged: every property is stated over
an abstract `Runner`, and every one is paired with a **named runner that
violates it**, closed by kernel `decide`. Each broken runner is a real
strategy, and one of them is the `||` that shipped:

| runner | the mistake | violates |
|---|---|---|
| `runnerFallback` | `A \|\| B` — revocation resolves to the next term | all four |
| `runnerBestEffort` | loops the targets, greens on whatever it reached | `Faithful` only |
| `runnerSufficientFallback` | substitutes, but only when the substitute suffices | all but `Faithful` |

`runnerCorrect` satisfies all four. The last two rows are the load-bearing
ones: they violate **disjoint** sets of properties, which is what shows
`Faithful` and `ActsAsNamed` are independent rather than two spellings of
one idea. That result is re-proved temporally in `specs/tla/degradation.tla`,
where the same two faults get a config each.

## The two results worth reading first

`degradation_is_unobservable` — under `runnerFallback`, the report is
**byte-identical** whether or not the credential was revoked, while the set
of repos actually touched is not. That pair is the incident: the same green
check over two different worlds. It is the formal content of the word
"silently".

`revoked_refuses_under_any_fallback` — `runnerCorrect` refuses a revoked
authority under *every* fallback the environment could supply, including one
that would comfortably suffice. Like `anon_refused_under_any_decision` in the
disclosure arc, the point is that this is not a capability question: a
revocation the caller can route around is not a revocation.

## Claim boundary

These are theorems about the model in `Authority.lean`. **They do not prove
that any deployed workflow refuses correctly**, and nothing here has observed
a live run. `content-catalog`'s workflows have never heard of these
definitions; a green `lake build` says the rules are coherent and that three
named strategies violate them — including the one that shipped. Closing this
arc is not closing `content-catalog#10`, and the two must not be reported as
one. See the README.
-/

namespace Keycard.Degradation

/-! ## Runners

A runner performs-or-refuses. It is handed the issuer's revocation record,
the authority the **policy named**, a fallback that happens to be present,
and the operation.

Handing it the fallback is deliberate, for `Signing.lean`'s reason: a runner
that *could* substitute and provably does not is a stronger statement than
one that was never offered the chance. And the fallback is genuinely
ambient here — `secrets.GITHUB_TOKEN` is injected into every workflow run
whether or not anyone asked for it, which is what makes `||` so easy to
write and so hard to notice. -/

/-- The performed-or-refused decision, together with what it actually did. -/
abbrev Runner := Keyring → Authority → Authority → Operation → Outcome

/-- **The `||` itself.** `${{ secrets.A || secrets.B }}`: if the first term
    is unusable, take the second. Named as its own function because it is
    the mechanism under study, not an implementation detail of the runners
    that use it. -/
def resolve (k : Keyring) (named fb : Authority) : Authority :=
  if k.live named then named else fb

/-- **The runner.** Acts only as the authority the policy named, only while
    that authority is live, and only when it covers the whole operation.
    Anything else refuses — including the partial case, which fails closed
    rather than shipping a subset. -/
def runnerCorrect : Runner := fun k named _ op =>
  if k.live named && op.covered named then
    { under := named, reached := op.targets, report := Report.success }
  else
    { under := named, reached := [], report := Report.refused }

/-- Broken: **the shipped `||`.** Resolve the credential, do whatever that
    credential can do, exit green. It never refuses, so the caller's only
    signal is a success that means nothing. -/
def runnerFallback : Runner := fun k named fb op =>
  { under   := resolve k named fb
  , reached := op.reached (resolve k named fb)
  , report  := Report.success }

/-- Broken: no substitution — it uses the named authority and nothing else
    — but it walks the targets and reports success on whatever it managed
    to touch. This is the `continue-on-error` loop, and it is the fault
    that survives fixing the `||`.

    This repo runs the same *shape* deliberately in
    `.github/workflows/front-desk-add.yml`, where both credentialed steps
    carry `continue-on-error: true`. That is not this bug: there the
    partial outcome is a design choice with a named backstop (the central
    sweep) and the artifact is a project card, not an attested catalog. The
    shape is only a defect when something downstream reads the green as
    completeness. -/
def runnerBestEffort : Runner := fun k named _ op =>
  if k.live named then
    { under := named, reached := op.reached named, report := Report.success }
  else
    { under := named, reached := [], report := Report.refused }

/-- Broken, and the most tempting of the three: substitute the fallback,
    but only go green when the fallback actually covers the whole
    operation. It never ships a partial result — it is `Faithful` — and it
    is still wrong, because the effects are now attributable to a principal
    the policy never named and the revocation bought nothing. "The weaker
    token could do this job anyway" is the argument this runner makes, and
    `runnerSufficientFallback_not_revocationCloses` is the answer. -/
def runnerSufficientFallback : Runner := fun k named fb op =>
  if op.covered (resolve k named fb) then
    { under := resolve k named fb, reached := op.targets, report := Report.success }
  else
    { under := resolve k named fb, reached := [], report := Report.refused }

/-! ## The properties, as predicates over runners -/

/-- **Acts as named.** If the caller was told the operation succeeded, the
    effects are attributable to the authority the policy named — not to
    whatever else was in scope. This is the issue's proposed property, and
    it is the one the `||` breaks first. -/
def ActsAsNamed (R : Runner) : Prop :=
  ∀ k named fb op, (R k named fb op).report = Report.success →
    (R k named fb op).under = named

/-- **Faithful reporting.** Success means the operation was performed *in
    full*. A run that touched a subset and reported success is a partial
    artifact wearing a complete artifact's signal — which is exactly how an
    incomplete catalog acquired full provenance. -/
def Faithful (R : Runner) : Prop :=
  ∀ k named fb op, (R k named fb op).report = Report.success →
    (R k named fb op).reached = op.targets

/-- **Revocation closes.** A revoked authority yields a refusal and no
    effects at all. The operational property: what a credential audit is
    *for* is that afterwards, the door is shut. -/
def RevocationCloses (R : Runner) : Prop :=
  ∀ k named fb op, k.live named = false →
    (R k named fb op).report = Report.refused ∧ (R k named fb op).reached = []

/-- **Fallback-blindness.** What else happens to be in the environment
    changes nothing. This is `AmbientBlind` (`Signing.lean`) and `EnvBlind`
    (`Disclosure.lean`) at a third boundary, and the same sentence applies:
    authority that ambient state can supply is not authority, it is a
    setting. `secrets.GITHUB_TOKEN` is ambient in the strictest sense —
    nobody puts it there. -/
def FallbackBlind (R : Runner) : Prop :=
  ∀ k named fb₁ fb₂ op, R k named fb₁ op = R k named fb₂ op

/-! ## `runnerCorrect` satisfies all four -/

theorem runnerCorrect_actsAsNamed : ActsAsNamed runnerCorrect := by
  intro k named fb op _
  simp only [runnerCorrect]
  split <;> rfl

theorem runnerCorrect_faithful : Faithful runnerCorrect := by
  intro k named fb op h
  by_cases hc : (k.live named && op.covered named) = true
  · simp [runnerCorrect, hc]
  · simp [runnerCorrect, hc] at h

theorem runnerCorrect_revocationCloses : RevocationCloses runnerCorrect := by
  intro k named fb op h
  simp [runnerCorrect, h]

theorem runnerCorrect_fallbackBlind : FallbackBlind runnerCorrect := by
  intro _ _ _ _ _; rfl

/-! ## Fixtures

Drawn from the 2026-08-16 credential audit and the four workflows it
degraded, and cited so the model can be checked against what happened. They
are fixtures of the **model**; evaluating them measures nothing about any
deployed workflow.

- **the org's repos** — one public (the catalog's own), two private. The
  private pair is what dropped out of the enumeration.
- **`fxBootstrap`** — `secrets.BOOTSTRAP_TOKEN`, the revoked PAT: org-wide
  `repo` scope, so read and write on everything.
- **`fxGithubToken`** — `secrets.GITHUB_TOKEN`, always present,
  repo-scoped and read-only by org default.
- **`fxAudit`** — the audit itself: authority `1` revoked. -/

/-- The catalog's own repo — public, and the only one the fallback reaches. -/
def fxSelf : Repo := { id := 1, isPrivate := false }

/-- Two private org repos. These are the ones that silently left the
    catalog. -/
def fxPrivateA : Repo := { id := 2, isPrivate := true }
def fxPrivateB : Repo := { id := 3, isPrivate := true }

def fxOrgRepos : List Repo := [fxSelf, fxPrivateA, fxPrivateB]

/-- `secrets.BOOTSTRAP_TOKEN` — org-wide `repo` scope. -/
def fxBootstrap : Authority :=
  { id := 1
  , grants :=
      [ { action := Action.read,  repo := fxSelf }
      , { action := Action.read,  repo := fxPrivateA }
      , { action := Action.read,  repo := fxPrivateB }
      , { action := Action.write, repo := fxSelf }
      , { action := Action.write, repo := fxPrivateA }
      , { action := Action.write, repo := fxPrivateB } ] }

/-- `secrets.GITHUB_TOKEN` — repo-scoped, read-only by org default. -/
def fxGithubToken : Authority :=
  { id := 2
  , grants := [ { action := Action.read, repo := fxSelf } ] }

/-- The credential audit: the PAT behind `secrets.BOOTSTRAP_TOKEN` revoked. -/
def fxAudit : Keyring := { revoked := [1] }

/-- The world before the audit. -/
def fxIntact : Keyring := { revoked := [] }

/-- The cross-repo catalog write — "visited every repo, wrote nothing,
    exited green". -/
def fxWriteCatalog : Operation := { action := Action.write, targets := fxOrgRepos }

/-- The org enumeration — the one that narrowed to public repos. -/
def fxEnumerate : Operation := { action := Action.read, targets := fxOrgRepos }

/-- A narrow operation the fallback genuinely covers: read the public repo.
    This exists for `runnerSufficientFallback`, whose defence is precisely
    that the substitute was good enough. -/
def fxReadSelf : Operation := { action := Action.read, targets := [fxSelf] }

/-- **The fallback is strictly weaker.** Checked, not asserted: every grant
    `secrets.GITHUB_TOKEN` carries, the PAT carried too, and not
    conversely. -/
theorem fxGithubToken_strictly_weaker :
    fxGithubToken.strictlyWeakerThan fxBootstrap = true := by decide

/-! ## The two results worth reading first -/

/-- **Degradation is unobservable.** Under the shipped `||`, the report is
    the same in a world where the credential is live and a world where it
    was revoked — `rfl`, because `runnerFallback` cannot produce any other
    report. -/
theorem degradation_is_unobservable (fb : Authority) (op : Operation) :
    (runnerFallback fxIntact fxBootstrap fb op).report
      = (runnerFallback fxAudit fxBootstrap fb op).report := rfl

/-- …and the effects are not the same. Same signal, different world: the
    write reached all three repos before the audit and none after it, and
    the caller was told `success` both times. This pair is the incident. -/
theorem degradation_changes_effects :
    (runnerFallback fxIntact fxBootstrap fxGithubToken fxWriteCatalog).reached
      ≠ (runnerFallback fxAudit fxBootstrap fxGithubToken fxWriteCatalog).reached := by
  decide

/-- **Refused under every fallback.** `runnerCorrect` refuses a revoked
    authority whatever else is in the environment — including a fallback
    that would cover the operation outright. The disclosure arc's
    `anon_refused_under_any_decision` makes the same move: some things are
    not policy questions. A revocation the caller can route around is not a
    revocation. -/
theorem revoked_refuses_under_any_fallback (k : Keyring) (named : Authority)
    (op : Operation) (h : k.live named = false) :
    ∀ fb : Authority, (runnerCorrect k named fb op).report = Report.refused := by
  intro fb
  simp [runnerCorrect, h]

/-! ## The counterexamples — each closed by kernel `decide` -/

/-- The `||` acts as a principal the policy never named. -/
theorem runnerFallback_not_actsAsNamed : ¬ ActsAsNamed runnerFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxWriteCatalog (by decide)) (by decide)

/-- **"Visited every repo, wrote nothing, exited green."** The write
    operation reports success having reached nothing at all. -/
theorem runnerFallback_not_faithful : ¬ Faithful runnerFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxWriteCatalog (by decide)) (by decide)

/-- Revocation does not close the door — it changes who is holding it. -/
theorem runnerFallback_not_revocationCloses : ¬ RevocationCloses runnerFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxWriteCatalog (by decide)).1 (by decide)

/-- And the outcome is decided by a credential nobody put there. -/
theorem runnerFallback_not_fallbackBlind : ¬ FallbackBlind runnerFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxBootstrap fxWriteCatalog) (by decide)

/-- `runnerCorrect` refuses the same request. The properties separate the
    two runners; this is what makes the counterexamples above more than a
    restatement of the definitions. -/
theorem runnerCorrect_refuses_revoked :
    (runnerCorrect fxAudit fxBootstrap fxGithubToken fxWriteCatalog).report
      = Report.refused := by decide

/-! ### The independence pair

`runnerBestEffort` and `runnerSufficientFallback` violate **disjoint** sets
of properties. Neither fix implies the other: stop substituting and you can
still ship a green partial; stop shipping partials and effects can still
land under an unnamed principal. -/

/-- Best-effort never substitutes… -/
theorem runnerBestEffort_actsAsNamed : ActsAsNamed runnerBestEffort := by
  intro k named fb op _
  simp only [runnerBestEffort]
  split <;> rfl

theorem runnerBestEffort_revocationCloses : RevocationCloses runnerBestEffort := by
  intro k named fb op h
  simp [runnerBestEffort, h]

theorem runnerBestEffort_fallbackBlind : FallbackBlind runnerBestEffort := by
  intro _ _ _ _ _; rfl

/-- …and still ships a partial artifact under a green check. The named
    authority here is live and honestly used; it simply never covered the
    whole operation, and nothing said so. -/
theorem runnerBestEffort_not_faithful : ¬ Faithful runnerBestEffort := fun h =>
  absurd (h fxIntact fxGithubToken fxGithubToken fxEnumerate (by decide)) (by decide)

/-- The other half of the pair: substituting only when the substitute
    suffices is genuinely `Faithful` — it never greens a partial result. -/
theorem runnerSufficientFallback_faithful : Faithful runnerSufficientFallback := by
  intro k named fb op h
  by_cases hc : op.covered (resolve k named fb) = true
  · simp [runnerSufficientFallback, hc]
  · simp [runnerSufficientFallback, hc] at h

/-- …and still lets a revoked authority's work proceed under someone else's
    identity. The revocation is correct, the capability check passes, and
    the door is open anyway. -/
theorem runnerSufficientFallback_not_revocationCloses :
    ¬ RevocationCloses runnerSufficientFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxReadSelf (by decide)).1 (by decide)

theorem runnerSufficientFallback_not_actsAsNamed :
    ¬ ActsAsNamed runnerSufficientFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxReadSelf (by decide)) (by decide)

/-- …and, like the shipped `||`, it lets the surrounding environment decide
    who acts. Stated so the table above is checked rather than believed:
    this runner violates every property except `Faithful`. -/
theorem runnerSufficientFallback_not_fallbackBlind :
    ¬ FallbackBlind runnerSufficientFallback := fun h =>
  absurd (h fxAudit fxBootstrap fxGithubToken fxBootstrap fxReadSelf) (by decide)

/-! ## The model as the executable checker

The reason to prefer `Bool` throughout, unchanged from `Claim.lean`: the
predicate a runner would consult and the predicate the theorems quantify
over are one artifact. `#guard` closes each of these by kernel evaluation,
and each states something the incident actually did. -/

-- Before the audit: the write reaches every repo in the org.
#guard (runnerFallback fxIntact fxBootstrap fxGithubToken fxWriteCatalog).reached = fxOrgRepos
-- After it: the same workflow, the same green report, and nothing written.
#guard (runnerFallback fxAudit fxBootstrap fxGithubToken fxWriteCatalog).reached = []
#guard (runnerFallback fxAudit fxBootstrap fxGithubToken fxWriteCatalog).report = Report.success
-- The enumeration does not fail either — it narrows.
#guard (runnerFallback fxAudit fxBootstrap fxGithubToken fxEnumerate).reached = [fxSelf]
-- And `runnerCorrect` refuses both, which is all a credential audit ever wanted.
#guard (runnerCorrect fxAudit fxBootstrap fxGithubToken fxWriteCatalog).report = Report.refused
#guard (runnerCorrect fxAudit fxBootstrap fxGithubToken fxEnumerate).report = Report.refused

/-- **The narrowing, exactly as it happened.** Every repo the degraded
    enumeration reached is public — the private ones dropped out of a
    catalog that is committed *and* SLSA-attested, so a partial artifact
    shipped with full provenance. The attestation is not wrong about what
    it signed; it is signing something nobody noticed had changed. -/
theorem fallback_enumeration_is_public_only :
    ((runnerFallback fxAudit fxBootstrap fxGithubToken fxEnumerate).reached).all
      (fun r => !r.isPrivate) = true := by decide

/-- And it is a strict subset: the enumeration lost repos rather than
    failing. -/
theorem fallback_enumeration_is_partial :
    (runnerFallback fxAudit fxBootstrap fxGithubToken fxEnumerate).reached ≠ fxOrgRepos := by
  decide

end Keycard.Degradation
