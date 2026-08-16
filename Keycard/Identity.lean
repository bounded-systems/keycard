import Keycard.Signing
/-!
# Identity provenance: vendor-blindness, and guest-injective attestation

Arc 3. Two questions, both asked on 2026-08-16, both theorem-shaped:

> If we removed GitHub from Claude cloud, how would we prove identity?

> Could OAuth on the MCP work as identity — how do MCP servers know who
> is connected?

The first is a **parametricity** question. The decided design (#520 option
b) has the gate evaluate an issuer-attested claim at admission. If that is
really the trust root, the accept decision must be invariant under
substitution of the *vendor* — the party that renders verification badges
against its own records — **including substitution of the empty vendor**.
`vsignerGate_vendorBlind` says the decided gate has that property, and
every theorem already proved of `signerCorrect` transfers under any vendor
because the proofs never mention one. The counterexample with content is
`vsignerBadge`: a gate shaped like today's deployed admission control
(`required_signatures` plus the Verified badge, the bridge #524 §6
measured). It is not vendor-blind, and with the vendor absent it refuses
everything, live claim or not — identity did not fail, the gate was
coupled.

The second is an **injectivity** question. A remote MCP server knows who
is connected as the OAuth account that authorized it — the *owner* axis.
Every session of one owner presents the same principal. (A local stdio
MCP server knows less still: "whoever spawned my process" is ambient
authority, already excluded by `AmbientBlind`.) Modeled as an attestor
whose subject map factors through the owner, this fails `Attributing`,
and `owner_grade_amplifies` shows the consequence: subject-equal guests
have identical signing power everywhere — one session claims, every
sibling signs. This is the measured Pathbase-lease limitation ("login is
the ONE predicate a session token can satisfy", `toolpath-pathbase.md`
2026-08-10) stated as a theorem. It is the same discipline as Arc 1's
`NeverReassigned`, one layer up: an identity root must name *guests*
injectively, which is the selection criterion for any vendor replacement —
per-room SPIFFE IDs and per-session JWTs pass; account-grade OAuth fails
by construction, whatever transport (MCP included) carries it. OAuth token
exchange changes the verdict only by changing the attestor: exchange a
per-session credential and the subject map is workload-grade again — the
transport was never the question.

## Claim boundary

Theorems about the model in `Claim.lean`. **They do not prove the org can
remove GitHub today** — today's deployed admission control is the
badge-shaped gate, and `vsignerBadge_dark_without_vendor` is this file
saying exactly that. Nothing here gates anything.
-/

namespace Keycard

/-! ## The vendor axis -/

/-- What a vendor (GitHub today) contributes at admission time that is not
    an issuer-attested claim: a verification verdict rendered against its
    own records — the Verified badge consumed by `required_signatures`. -/
structure Vendor where
  badge : Guest → Issue → Time → Bool

/-- The vendor present and agreeable: every badge renders. -/
def Vendor.present : Vendor := ⟨fun _ _ _ => true⟩

/-- The empty vendor — "GitHub removed." No verdict for anyone, ever. -/
def Vendor.absent : Vendor := ⟨fun _ _ _ => false⟩

/-- A gate that is *offered* the vendor. As with `Signer` and `Ambient`:
    a gate that could consult the badge and provably does not is a stronger
    statement than one that was never offered it. -/
abbrev VSigner := Vendor → Ledger → Ambient → Guest → Issue → Time → Bool

/-- **Vendor-blindness.** The decision is invariant under vendor
    substitution — including substitution of `Vendor.absent`. -/
def VendorBlind (S : VSigner) : Prop :=
  ∀ v₁ v₂ L a g i t, S v₁ L a g i t = S v₂ L a g i t

/-- The decided gate (#520 option b): evaluate the claim at admission;
    the vendor is not consulted. -/
def vsignerGate : VSigner := fun _ L a g i t => signerCorrect L a g i t

/-- Today's deployed shape: the vendor's verdict AND'd into admission —
    `required_signatures` plus the badge, per the bridge #524 §6 measured. -/
def vsignerBadge : VSigner := fun v L _ g i t => v.badge g i t && holdsClaim L g i t

/-- **The gate is vendor-blind.** -/
theorem vsignerGate_vendorBlind : VendorBlind vsignerGate :=
  fun _ _ _ _ _ _ _ => rfl

/-- **The question, answered as stated:** with the vendor removed, the gate
    decides exactly what it decided with the vendor present. -/
theorem vendor_removal_invariant (L : Ledger) (a : Ambient) (g : Guest) (i : Issue) (t : Time) :
    vsignerGate Vendor.absent L a g i t = vsignerGate Vendor.present L a g i t := rfl

/-! Every property proved of `signerCorrect` transfers to the gate under
    **any** vendor. These are one-line reuses, and that is the finding: the
    Arc-2 proofs never mention a vendor, so removing one cannot invalidate
    them. -/

theorem vsignerGate_sound (v : Vendor) : Sound (vsignerGate v) :=
  signerCorrect_sound

theorem vsignerGate_ambientBlind (v : Vendor) : AmbientBlind (vsignerGate v) :=
  signerCorrect_ambientBlind

theorem vsignerGate_released_revokes (v : Vendor) (L : Ledger) (a : Ambient)
    (g : Guest) (i : Issue) (t : Time)
    (hrel : ∀ c, c ∈ L.claims → c.guest = g → c.issue = i →
      ∃ r, c.release = some r ∧ r ≤ t) :
    vsignerGate v L a g i t = false :=
  released_revokes L a g i t hrel

theorem vsignerGate_no_amplification (v : Vendor) (L : Ledger) (a : Ambient)
    (g : Guest) (i j : Issue) (t : Time)
    (hij : i ≠ j) (honly : ∀ c, c ∈ L.claims → c.issue = i) :
    vsignerGate v L a g j t = false :=
  no_amplification L a g i j t hij honly

/-- Badge-gating is **not** vendor-blind: with a live claim on the ledger,
    removing the vendor flips the decision. -/
theorem vsignerBadge_not_vendorBlind : ¬ VendorBlind vsignerBadge := fun h =>
  absurd (h Vendor.present Vendor.absent fxLedgerLive Ambient.stock fxGuest fxIssue280 5)
    (by decide)

/-- What vendor removal does to a badge-gated org: every request refused,
    live claim or not. The org goes dark not because identity failed but
    because admission was coupled to the vendor's verdict. -/
theorem vsignerBadge_dark_without_vendor (L : Ledger) (a : Ambient)
    (g : Guest) (i : Issue) (t : Time) :
    vsignerBadge Vendor.absent L a g i t = false := rfl

/-! ## The attestor axis -/

/-- An attestor names guests: the subject map of whatever identity root
    writes claim records. Arc 1's `SubScheme` is about how an issuer
    derives a subject from an authentication context; this is the layer
    above — *which entity* the subject can name at all. -/
structure Attestor where
  subject : Guest → Nat

/-- **Per-guest attribution.** Distinct guests get distinct subjects. An
    attestor that cannot tell two guests apart writes records the gate
    cannot tell apart either — the `NeverReassigned` discipline, applied
    to guests. -/
def Attributing (A : Attestor) : Prop :=
  ∀ g₁ g₂ : Guest, A.subject g₁ = A.subject g₂ → g₁ = g₂

/-- A workload attestor: the subject carries the guest itself — a SPIFFE ID
    per room, a session JWT per session. -/
def attestorWorkload : Attestor := ⟨fun g => g.id⟩

/-- An owner-grade attestor: the subject carries only the account that
    authorized — all OAuth on a remote MCP server (or any account-scoped
    token) can say. `owner` maps each guest to its authorizing account. -/
def attestorOwner (owner : Guest → Nat) : Attestor := ⟨owner⟩

theorem attestorWorkload_attributing : Attributing attestorWorkload := by
  intro g₁ g₂ h
  cases g₁; cases g₂
  exact congrArg Guest.mk h

/-- Every session of this account: the owner map is constant. -/
def fxOwnerMap : Guest → Nat := fun _ => 9

/-- A second guest — a sibling session of the same owner. -/
def fxGuest2 : Guest := ⟨2⟩

/-- Owner-grade attestation is not attributing: two sessions of one
    account share a subject. -/
theorem attestorOwner_not_attributing : ¬ Attributing (attestorOwner fxOwnerMap) := fun h =>
  absurd (h fxGuest fxGuest2 rfl) (by decide)

/-- Under an attributing attestor the amplification hypothesis below is
    unsatisfiable: distinct guests never alias. -/
theorem attributing_no_aliasing (A : Attestor) (hA : Attributing A)
    (g₁ g₂ : Guest) (hne : g₁ ≠ g₂) : A.subject g₁ ≠ A.subject g₂ :=
  fun h => hne (hA g₁ g₂ h)

/-! ## What a subject-keyed ledger can and cannot say

A door fronted by an attestor learns a *subject*, not a guest — so what it
records is keyed by subject. `holdsClaimVia` is `holdsClaim` for that
ledger. Everything then turns on whether the subject map is injective. -/

/-- A claim record as an attestor-fronted door can write it: keyed by the
    subject the attestor authenticated. -/
structure SubjectClaim where
  subject : Nat
  issue   : Issue
  since   : Time
  release : Option Time
deriving DecidableEq, Repr

def SubjectClaim.live (c : SubjectClaim) (t : Time) : Bool :=
  decide (c.since ≤ t) &&
    (match c.release with
     | none   => true
     | some r => decide (t < r))

/-- The lookup a subject can perform: is a live record binding subject `s`
    to `i` at `t` on the ledger? Deliberately a function of the *subject* —
    the door never sees more. -/
def holdsClaimSubj (s : Nat) (L : List SubjectClaim) (i : Issue) (t : Time) : Bool :=
  L.any fun c => decide (c.subject = s) && decide (c.issue = i) && c.live t

/-- The predicate over a subject-keyed ledger: `g` holds `i` at `t` iff a
    live record binds *`g`'s subject* to `i`. Factoring through
    `holdsClaimSubj` is the model saying structurally that an
    attestor-fronted door learns a subject, not a guest. -/
def holdsClaimVia (A : Attestor) (L : List SubjectClaim)
    (g : Guest) (i : Issue) (t : Time) : Bool :=
  holdsClaimSubj (A.subject g) L i t

/-- **Owner-grade identity amplifies across guests.** Subject-equal guests
    have identical signing power at every ledger, issue, and time: one
    session claims, every sibling signs. The MCP-OAuth question, answered:
    the account axis cannot carry per-guest identity, whatever transport
    presents it. The proof is one `congrArg` — the door's view *is* the
    subject, so equal subjects mean equal power, definitionally. -/
theorem owner_grade_amplifies (A : Attestor) (g₁ g₂ : Guest)
    (hsub : A.subject g₁ = A.subject g₂)
    (L : List SubjectClaim) (i : Issue) (t : Time) :
    holdsClaimVia A L g₁ i t = holdsClaimVia A L g₂ i t :=
  congrArg (fun s => holdsClaimSubj s L i t) hsub

/-! ## The counterexample, run

Subject `9` — the shared owner — holds a live claim on `prx#280`. Under
owner-grade attestation both sessions sign, including the one that never
claimed. Under workload attestation (ledger keyed by guest 1's subject),
only the claimant signs. Closed by kernel `decide` via `#guard`. -/

/-- The owner's account holds a live claim on `prx#280`. -/
def fxSubjLedgerOwner : List SubjectClaim := [⟨9, fxIssue280, 0, none⟩]

/-- Guest 1's workload subject holds the same claim. -/
def fxSubjLedgerWorkload : List SubjectClaim := [⟨1, fxIssue280, 0, none⟩]

-- Owner-grade: the claimant signs — and so does the sibling that never claimed.
#guard holdsClaimVia (attestorOwner fxOwnerMap) fxSubjLedgerOwner fxGuest  fxIssue280 5 = true
#guard holdsClaimVia (attestorOwner fxOwnerMap) fxSubjLedgerOwner fxGuest2 fxIssue280 5 = true
-- Workload-grade: the claimant signs; the sibling is refused.
#guard holdsClaimVia attestorWorkload fxSubjLedgerWorkload fxGuest  fxIssue280 5 = true
#guard holdsClaimVia attestorWorkload fxSubjLedgerWorkload fxGuest2 fxIssue280 5 = false

end Keycard
