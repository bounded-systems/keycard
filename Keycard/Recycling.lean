import Keycard.Model

/-!
# The counterexample: name-based subjects under recycling

The pre-2026 GitHub Actions subject format built the `sub` from names alone
(`repo:OWNER/REPO:...`). GitHub names are recyclable: delete or rename an
account and the label returns to the pool. This file exhibits the violation
as a two-instant world — `acme/widget` changes hands, and the name-based
scheme mints the same subject for two distinct principals.

This is the attack GitHub's 2026-04-23 changelog closes with immutable
subject claims (`repo:OWNER@OWNER_ID/REPO@REPO_ID:...`).
-/

namespace Keycard

/-- The pre-2026 shape: the subject is the name, nothing else. -/
def nameSub : SubScheme Name := fun c => c.name

/-- A world in which every name changes hands at t = 1: principal 0 holds
    everything at instant 0, principal 1 thereafter. One recycled name is
    all the theorem needs; giving every name the same history keeps the
    witness small. -/
def recycledWorld : Ownership := fun t _ =>
  if t = 0 then some ⟨0⟩ else some ⟨1⟩

/-- `acme/widget`, yesterday's holder. -/
def yesterday : Ctx := ⟨0, ⟨"acme/widget"⟩, ⟨0⟩⟩

/-- `acme/widget`, today's holder — a different entity, same label. -/
def today : Ctx := ⟨1, ⟨"acme/widget"⟩, ⟨1⟩⟩

/-- **The violation.** Under name recycling, the name-based scheme does not
    satisfy "never reassigned": both issuances are honest, the subjects are
    equal, and the principals are not. A relying party matching this `sub`
    admits yesterday's guest to today's room. -/
theorem nameSub_not_neverReassigned :
    ¬ NeverReassigned recycledWorld nameSub := by
  intro h
  have hy : yesterday.honest recycledWorld := rfl
  have ht : today.honest recycledWorld := rfl
  have : yesterday.principal = today.principal := h yesterday today hy ht rfl
  simp [yesterday, today] at this

end Keycard
