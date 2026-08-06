import Keycard.Model

/-!
# Soundness: subjects that embed an immutable ID

The 2026 GitHub format embeds numeric IDs next to the names
(`repo:OWNER@OWNER_ID/REPO@REPO_ID:...`). The IDs are the issuer's
identifier assignment for principals; the trust assumption — stated here
as `IdDiscipline`, not smuggled in — is that the issuer never assigns one
ID to two entities. Given that single assumption, the embedding scheme
satisfies "never reassigned" in **every** world, recycling or not: the
name may travel, the ID pins the principal.
-/

namespace Keycard

/-- The issuer's identifier assignment: which numeric ID each principal
    carries (`databaseId` in GitHub terms). -/
def IdAssignment := Principal → Nat

/-- The trust assumption, explicit and minimal: the issuer never assigns
    the same ID to two distinct principals. Everything downstream is
    conditional on exactly this. -/
def IdDiscipline (idOf : IdAssignment) : Prop :=
  ∀ p₁ p₂ : Principal, idOf p₁ = idOf p₂ → p₁ = p₂

/-- The 2026 shape: the subject carries the name *and* the immutable ID.
    Structured as a pair — the string encoding and its `@` delimiter are a
    separate concern (see `Matcher.lean`). -/
def idSub (idOf : IdAssignment) : SubScheme (Name × Nat) :=
  fun c => (c.name, idOf c.principal)

/-- **Soundness.** Under ID discipline, the embedding scheme is
    never-reassigned in every world — including `recycledWorld`. The
    quantifier over `w` is the point: no assumption about name hygiene is
    needed once the ID rides along. -/
theorem idSub_neverReassigned (idOf : IdAssignment) (h : IdDiscipline idOf) :
    ∀ w : Ownership, NeverReassigned w (idSub idOf) := by
  intro _ c₁ c₂ _ _ heq
  exact h _ _ (congrArg Prod.snd heq)

/-- The counterexample world is not special-cased away: the same scheme is
    sound *there* too, with the identity assignment as witness. -/
example : NeverReassigned recycledWorld (idSub Principal.entity) :=
  idSub_neverReassigned Principal.entity
    (fun p₁ p₂ h => by cases p₁; cases p₂; cases h; rfl)
    recycledWorld

end Keycard
