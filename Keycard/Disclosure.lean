import Keycard.Transcript
/-!
# Session-transcript disclosure: the theorems

Five properties, each matching a decision that is currently unmade or an
implementation that is currently deployed.

## How these avoid being vacuous

The discipline is `Signing.lean`'s, unchanged: every property is stated over
an abstract `Policy`, and every one is paired with a **named policy that
violates it**, closed by kernel `decide`. Each broken policy is a real
strategy — three of them are running or proposed right now, and one of them
is the org's own new share step.

| policy | the mistake | violates | where it lives |
|---|---|---|---|
| `policyBareShare` | uploads with whatever auth it has, falling back to anonymous | revocability, decision-grounding | `path share` today, measured in `preflight_auth` |
| `policyEnvVar` | an environment variable decides disclosure | ambient-blindness, decision-grounding | **this org's `share-session.sh`** |
| `policyUnlistedIsEnough` | unlisted treated as a privacy property | private-guarding | the tempting reading of the vendor default |
| `policyFailOpen` | absence of a decision read as permission | decision-grounding | the failure mode a fail-open guard invites |

`policyCorrect` satisfies all five. That the properties *separate* these
five policies is the evidence that they have content.

## The two results worth reading first

`unlisted_published_is_public` — a UUID-addressable upload whose URL is
posted on a public pull request is readable by everyone. "Unlisted" sounds
like a privacy property and is not one; the vendor's setting and this org's
publishing decision compose, and the composition is public.

`anon_refused_under_any_decision` — the anonymous endpoint is refused under
*every* decision the owner could possibly write, including the most
permissive one. It is not a policy question at all, because an anonymous
upload has no owner and therefore cannot be withdrawn by anyone. This is why
the safe default is not "share less" but "share nothing until an account we
control is on the other end".

## Claim boundary

These are theorems about the model in `Transcript.lean`. **They do not prove
that any deployed sharer refuses correctly.** Nothing consults these
definitions; `share-session.sh` has never heard of them. What they establish
is that the rules are coherent and that four named strategies violate them —
including the one currently shipped. See the README.
-/

namespace Keycard.Disclosure

/-! ## Policies

A policy decides share-or-refuse. It is handed the owner's decision record,
the session's ambient state, the session, and the upload it is being asked
about. Handing it the `Env` is deliberate, for `Signing.lean`'s reason: a
policy that *could* read the environment and provably does not is a stronger
statement than one that was never offered it. -/

/-- The share-or-refuse decision. -/
abbrev Policy := Policybook → Env → Session → Upload → Bool

/-- Redaction demanded by the decision is present on the upload. -/
def okRedaction (d : Decision) (u : Upload) : Bool :=
  !d.requireRedaction || u.redacted

/-- **The policy.** Revocable, under the decided account, redacted if the
    decision says so, and private content only if the decision allows it. -/
def policyCorrect : Policy := fun book _ s u =>
  match book with
  | none   => false
  | some d =>
      u.revocable
        && decide (u.owner = Owner.account d.owner)
        && okRedaction d u
        && (!s.touchedPrivate || d.allowPrivate)

/-- Broken: today's `path share`. It has no policy — it uploads, and when
    credentials are absent or rejected it falls back to the anonymous
    endpoint rather than refusing (`preflight_auth`, measured upstream). -/
def policyBareShare : Policy := fun _ _ _ _ => true

/-- Broken: **this org's own `share-session.sh`.** An environment variable
    decides disclosure. It is genuinely safe against the anonymous fallback
    — `u.revocable` is the `--name` guard, and it holds — but the authority
    to disclose comes from ambient state, which is #521's `commit.gpgsign`
    fault wearing different clothes. -/
def policyEnvVar : Policy := fun _ e _ u => e.shareEnv && u.revocable

/-- Broken: unlisted treated as sufficient protection for private content. -/
def policyUnlistedIsEnough : Policy := fun _ _ _ u =>
  u.revocable && decide (u.listing = Listing.unlisted)

/-- Broken: no decision record read as permission rather than as refusal. -/
def policyFailOpen : Policy := fun book e s u =>
  match book with
  | none   => u.revocable
  | some d => policyCorrect (some d) e s u

/-! ## The properties, as predicates over policies -/

/-- **Revocability.** Nothing may leave that cannot afterwards be withdrawn.
    The irreversibility property: an upload is not a lease. -/
def Revocable (P : Policy) : Prop :=
  ∀ b e s u, P b e s u = true → u.revocable = true

/-- **Decision-grounding.** With no owner decision on record, nothing is
    permitted. `none` is today's state, so this is the property that decides
    whether the org is currently sharing by accident. -/
def DecisionGrounded (P : Policy) : Prop :=
  ∀ e s u, P none e s u = false

/-- **Ambient-blindness.** Session-mutable state can neither confer
    disclosure nor withhold it. Both directions matter, exactly as in
    `Signing.lean`: authority that mutable local state can toggle is not
    authority, it is a setting. -/
def AmbientBlind (P : Policy) : Prop :=
  ∀ b e₁ e₂ s u, P b e₁ s u = P b e₂ s u

/-- **Private-guarding.** A session that read private material discloses
    only under a decision that explicitly allows it. -/
def PrivateGuarded (P : Policy) : Prop :=
  ∀ d e s u, s.touchedPrivate = true → P (some d) e s u = true → d.allowPrivate = true

/-- **Redaction honored.** A decision demanding redaction is not satisfiable
    by an unredacted upload. -/
def RedactionHonored (P : Policy) : Prop :=
  ∀ d e s u, d.requireRedaction = true → P (some d) e s u = true → u.redacted = true

/-! ## Facts about the model itself

These two are the results that answer the open questions, and neither is
about any policy. -/

/-- **Unlisted is not private.** Once the URL is published, the listing
    setting confers nothing. -/
theorem unlisted_published_is_public (u : Upload)
    (hl : u.listing = Listing.unlisted) (hp : u.urlPublished = true) :
    u.audience = Audience.everyone := by
  simp [Upload.audience, hl, hp]

/-- **Anonymous uploads are irrevocable.** No owner, so no account from
    which to delete. -/
theorem anon_never_revocable (u : Upload) (h : u.owner = Owner.anon) :
    u.revocable = false := by
  simp [Upload.revocable, h]

/-- **The anonymous endpoint is refused under every decision the owner could
    write** — including the most permissive one. Disclosure policy cannot
    reach it, because the defect is that nothing can withdraw it. -/
theorem anon_refused_under_any_decision (d : Decision) (e : Env) (s : Session) :
    policyCorrect (some d) e s uploadAnon = false := by
  simp [policyCorrect, uploadAnon, Upload.revocable]

/-! ## `policyCorrect` satisfies all five -/

theorem policyCorrect_revocable : Revocable policyCorrect := by
  intro b e s u h
  cases b with
  | none   => simp [policyCorrect] at h
  | some d =>
      simp only [policyCorrect, Bool.and_eq_true] at h
      exact h.1.1.1

theorem policyCorrect_decisionGrounded : DecisionGrounded policyCorrect := by
  intro _ _ _; rfl

theorem policyCorrect_ambientBlind : AmbientBlind policyCorrect := by
  intro b _ _ _ _
  cases b <;> rfl

theorem policyCorrect_privateGuarded : PrivateGuarded policyCorrect := by
  intro d e s u hp h
  simp only [policyCorrect, Bool.and_eq_true] at h
  have := h.2
  simp only [hp, Bool.not_true, Bool.false_or] at this
  exact this

theorem policyCorrect_redactionHonored : RedactionHonored policyCorrect := by
  intro d e s u hr h
  simp only [policyCorrect, Bool.and_eq_true] at h
  have := h.1.2
  simp only [okRedaction, hr, Bool.not_true, Bool.false_or] at this
  exact this

/-! ## The counterexamples — each closed by kernel `decide` -/

/-- Today's `path share` permits an upload nothing can withdraw. -/
theorem policyBareShare_not_revocable : ¬ Revocable policyBareShare := by
  intro h
  exact absurd (h none Env.stock Session.publicOnly uploadAnon rfl) (by decide)

/-- …and permits it with no owner decision in existence. -/
theorem policyBareShare_not_decisionGrounded : ¬ DecisionGrounded policyBareShare := by
  intro h
  exact absurd (h Env.stock Session.publicOnly uploadAnon) (by decide)

/-- **The org's own share step is not ambient-blind.** One `export` flips
    the disclosure decision. -/
theorem policyEnvVar_not_ambientBlind : ¬ AmbientBlind policyEnvVar := by
  intro h
  exact absurd (h none Env.stock Env.shareOn Session.publicOnly uploadAuthed) (by decide)

/-- …and it discloses with no owner decision on record. -/
theorem policyEnvVar_not_decisionGrounded : ¬ DecisionGrounded policyEnvVar := by
  intro h
  exact absurd (h Env.shareOn Session.publicOnly uploadAuthed) (by decide)

/-- But it *is* revocable — the `--name` guard against the anonymous
    fallback genuinely holds. Recorded so the counterexamples above are read
    as "unsound authority", not "unsafe upload". -/
theorem policyEnvVar_revocable : Revocable policyEnvVar := by
  intro b e s u h
  simp only [policyEnvVar, Bool.and_eq_true] at h
  exact h.2

/-- Unlisted is not a substitute for a decision about private content. -/
theorem policyUnlistedIsEnough_not_privateGuarded :
    ¬ PrivateGuarded policyUnlistedIsEnough := by
  intro h
  exact absurd
    (h Decision.publicOnly Env.stock Session.readPrivate uploadAuthed
      (by decide) (by decide)) (by decide)

/-- And it ignores a redaction requirement. -/
theorem policyUnlistedIsEnough_not_redactionHonored :
    ¬ RedactionHonored policyUnlistedIsEnough := by
  intro h
  exact absurd
    (h Decision.privateRedacted Env.stock Session.readPrivate uploadAuthed
      (by decide) (by decide)) (by decide)

/-- Absence of a decision is not permission. -/
theorem policyFailOpen_not_decisionGrounded : ¬ DecisionGrounded policyFailOpen := by
  intro h
  exact absurd (h Env.stock Session.publicOnly uploadAuthed) (by decide)

/-! ## The guest invariant and the capstone -/

/-- **No sequence of session actions writes a decision.** The disclosure
    analogue of `holdsClaim_guest_invariant`: `GuestStep` has no constructor
    that touches `book`, and this turns that absence into a checked
    property. -/
theorem decision_guest_invariant (w : World) (ss : List GuestStep) :
    (w.run ss).book = w.book := by
  induction ss generalizing w with
  | nil => rfl
  | cons s ss ih => simp [World.run, World.step, ih]

/-- **Capstone: no session action discloses anything.** Starting from
    today's state — no owner decision — no sequence of session actions,
    of any length, yields a permitted share under `policyCorrect`. The
    session cannot talk itself into disclosure. -/
theorem no_guest_disclosure (e : Env) (ss : List GuestStep) (s : Session) (u : Upload) :
    policyCorrect (World.run { book := none, env := e } ss).book
                  (World.run { book := none, env := e } ss).env s u = false := by
  rw [decision_guest_invariant]
  rfl

/-! ## The executable side

`#guard` closes each of these by kernel evaluation, so the same definitions
the theorems quantify over are the ones a checker would run. Each states
where the org actually is. -/

/-- Today: no decision, a session that read this private repo, an anonymous
    upload. Refused. -/
example : policyCorrect none Env.shareOn Session.readPrivate uploadAnon = false := by decide

/-- Today's `path share` in the same situation: permitted. That is the gap. -/
example : policyBareShare none Env.shareOn Session.readPrivate uploadAnon = true := by decide

/-- The narrowest useful decision permits a public-repo session. -/
example :
    policyCorrect (some Decision.publicOnly) Env.stock Session.publicOnly uploadAuthed = true := by
  decide

/-- The same decision refuses the private-repo session. -/
example :
    policyCorrect (some Decision.publicOnly) Env.stock Session.readPrivate uploadAuthed = false := by
  decide

/-- Permitting private repos with redaction required refuses the unredacted
    upload and permits the redacted one. -/
example :
    policyCorrect (some Decision.privateRedacted) Env.stock Session.readPrivate uploadAuthed
      = false := by decide

example :
    policyCorrect (some Decision.privateRedacted) Env.stock Session.readPrivate uploadRedacted
      = true := by decide

/-- The unlisted upload on a public PR is readable by everyone. -/
example : uploadAuthed.audience = Audience.everyone := by decide

end Keycard.Disclosure
