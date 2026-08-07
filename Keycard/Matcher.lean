import Keycard.Model
import Keycard.Recycling
import Keycard.Soundness

/-!
# Relying parties: what a matcher can and cannot recover

A relying party is a door reader: it sees a token's claims and decides.
Two shapes exist in the wild:

* **sub-only** (Azure- and AWS-shaped): the trust policy matches the `sub`
  value, nothing else. Sound iff the `sub` itself embeds the immutable ID.
* **arbitrary-claim** (GCP- and Vault-shaped): the policy may match any
  claim — in particular the long-standing immutable side-claims
  (`repository_id`, `repository_owner_id`), which predate the 2026 `sub`
  reshape. Such a policy recovers soundness even under a mutable `sub`.

Plus the migration gotcha, proved: a `repo:ORG/*` **string** wildcard
written against the mutable format silently stops matching once the
subject flips to `ORG@ID/...` — the pattern fails closed, but a policy
that *combined* wildcards is now trusting whichever arm still matches.
-/

namespace Keycard

/-- What a relying party means by "this door opens only for `p`": across
    all honest issuances in the world, any token the policy accepts was
    minted for `p`. -/
def SoundFor {α : Type} (w : Ownership) (f : SubScheme α)
    (accept : α → Bool) (p : Principal) : Prop :=
  ∀ c : Ctx, c.honest w → accept (f c) = true → c.principal = p

/-- A sub-only policy pinning the exact name `acme/widget`. -/
def pinName : Name → Bool := fun n => n == ⟨"acme/widget"⟩

/-- **Sub-only over a mutable sub is unsound under recycling**: the policy
    that pins yesterday's holder also opens for today's. Concretely: it is
    `SoundFor` no principal at all — each holder's honest token defeats the
    claim that the door is theirs alone. -/
theorem pinName_unsound :
    ¬ ∃ p : Principal, SoundFor recycledWorld nameSub pinName p := by
  intro ⟨p, h⟩
  have h₀ : yesterday.principal = p := h yesterday rfl rfl
  have h₁ : today.principal = p := h today rfl rfl
  simp [yesterday, today] at h₀ h₁
  rw [← h₀] at h₁
  simp at h₁

/-- A sub-only policy over the ID-embedding sub, pinning name *and* ID. -/
def pinNameAndId (n : Name) (i : Nat) : Name × Nat → Bool :=
  fun s => s.1 == n && s.2 == i

/-- **Sub-only over the immutable sub is sound**, in every world, for the
    principal carrying the pinned ID — provided the issuer keeps ID
    discipline. The Azure/AWS shape is fine *if* the sub embeds the ID. -/
theorem pinNameAndId_sound (idOf : IdAssignment) (hd : IdDiscipline idOf)
    (w : Ownership) (n : Name) (p : Principal) :
    SoundFor w (idSub idOf) (pinNameAndId n (idOf p)) p := by
  intro c _ hacc
  simp [pinNameAndId, idSub] at hacc
  exact hd _ _ hacc.2

/-- An arbitrary-claim policy: it sees the whole context's claim surface.
    (In the deployment this is `bound_claims` / attribute mapping; in the
    model, a predicate on `Ctx` composed with what the token carries. The
    side-claim `repository_id` is `idOf c.principal` — issued alongside a
    possibly-mutable sub.) -/
def pinIdClaim (idOf : IdAssignment) (i : Nat) : Ctx → Bool :=
  fun c => idOf c.principal == i

/-- **Claim-matching recovers soundness under a mutable sub**: pin the
    `repository_id` side-claim and the mutable `sub` can say whatever it
    likes — sound in every world, no sub reshape required. This is why
    claim-flexible relying parties could pin IDs years before the 2026
    flip. -/
theorem pinIdClaim_sound (idOf : IdAssignment) (hd : IdDiscipline idOf)
    (w : Ownership) (p : Principal) :
    ∀ c : Ctx, c.honest w → pinIdClaim idOf (idOf p) c = true → c.principal = p := by
  intro c _ hacc
  simp [pinIdClaim] at hacc
  exact hd _ _ hacc

/-! ## The wildcard corollary, on strings

The two subject *encodings*, and the prefix pattern a `repo:ORG/*` policy
compiles to. Decidable instances — the proofs are `by decide`, i.e. the
kernel checks the actual strings. -/

/-- Mutable encoding: `OWNER/REPO`. -/
def mutableSub (owner repo : String) : String := owner ++ "/" ++ repo

/-- Immutable encoding: `OWNER@OWNER_ID/REPO@REPO_ID` (the `@` delimiter,
    per the 2026-06-10 changelog correction). -/
def immutableSub (owner : String) (ownerId : Nat) (repo : String) (repoId : Nat) : String :=
  owner ++ "@" ++ toString ownerId ++ "/" ++ repo ++ "@" ++ toString repoId

/-- Prefix over `List Char`, written out so the kernel can evaluate it —
    `String.isPrefixOf`'s efficient implementation does not reduce under
    `decide`, and these theorems should be checked by the kernel, not the
    compiler (`native_decide` widens the trusted base for no gain here). -/
def isPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

/-- What `repo:ORG/*` means to a string matcher: `ORG/` is a prefix. -/
def orgWildcard (org sub : String) : Bool :=
  isPrefix (org ++ "/").toList sub.toList

/-- The wildcard matches the mutable encoding… -/
theorem wildcard_matches_mutable :
    orgWildcard "acme" (mutableSub "acme" "widget") = true := by decide

/-- …and silently stops matching the immutable one: `acme@7241` is not
    `acme`. A trust policy carrying `repo:acme/*` breaks — closed — the
    moment the org's repos flip. Proved on the strings themselves. -/
theorem wildcard_misses_immutable :
    orgWildcard "acme" (immutableSub "acme" 7241 "widget" 90513) = false := by decide

/-- The fixed wildcard pins the org *with its ID* — and matches again. -/
theorem wildcard_with_id_matches :
    orgWildcard ("acme@" ++ toString 7241)
      (immutableSub "acme" 7241 "widget" 90513) = true := by decide

end Keycard
