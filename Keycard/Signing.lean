import Keycard.Claim
/-!
# Claim-bound signing: the theorems

Five properties, each matching a failure that has actually occurred. The
headline is a biconditional, and the `iff` is the point: soundness alone
permits a system where the claim exists and signing works regardless —
which is exactly the state the org is in today, where signing is available
and the claim grants nothing.

## How these theorems avoid being vacuous

A property proved only of the implementation that satisfies it by
construction proves nothing about the property. So each theorem here is
stated over an abstract `Signer`, and each one is accompanied by a
**named signer that violates it** — a counterexample closed by kernel
`decide`. Every one of those broken signers is a real implementation
strategy, not a strawman:

| signer | the mistake | violates | history |
|---|---|---|---|
| `signerEverClaimed` | checks the claim exists, never that it is live | soundness | #435 — a stale `claimed` label as a standing grant |
| `signerRepoScoped` | mints a repo-scoped credential | soundness (at a second issue) | the natural implementation of an issue-scoped grant |
| `signerSelfAsserted` | trusts a guest-presented claim record | soundness, ambient-blindness | `claim-ticket.yml` is a `workflow_dispatch` anyone can call |
| `signerAmbient` | consults local git config | ambient-blindness | #521 — repo-local `commit.gpgsign` decided attributability |

`signerCorrect` satisfies all of them. That the properties *separate* these
five signers is the evidence that they have content.

## Claim boundary

These are theorems about the model in `Claim.lean`. **They do not prove
that any deployed signer refuses correctly.** Whether `keeperd` implements
these rules is a conformance question with its own evidence; see the README.
-/

namespace Keycard

/-! ## Signers

A signer decides sign-or-refuse. It is handed the issuer's ledger, the
guest's ambient state, and the (guest, issue, time) it is being asked
about. Handing it the `Ambient` is deliberate: a signer that *could* read
local config and provably does not is a stronger statement than one that
was never offered it. -/

/-- The sign-or-refuse decision. In the intended deployment this is the
    predicate `keeperd` runs. -/
abbrev Signer := Ledger → Ambient → Guest → Issue → Time → Bool

/-- **The signer.** Issuer-attested, issue-scoped, evaluated at `t`. -/
def signerCorrect : Signer := fun L _ g i t => holdsClaim L g i t

/-- Broken: "has this guest ever claimed this issue?" — ignores liveness,
    so a released claim still signs (#435). -/
def signerEverClaimed : Signer := fun L _ g i _ =>
  L.claims.any fun c => decide (c.guest = g) && decide (c.issue = i)

/-- Broken: the credential is scoped to the repo, so a claim on any issue
    signs for every issue in that repo. -/
def signerRepoScoped : Signer := fun L _ g i t =>
  L.claims.any fun c => decide (c.guest = g) && decide (c.issue.repo = i.repo) && c.live t

/-- Broken: accepts a claim record the guest presented about itself. -/
def signerSelfAsserted : Signer := fun L a g i t =>
  holdsClaim L g i t || a.asserted.any fun c => c.binds g i t

/-- Broken: local `commit.gpgsign` decides whether the effect is
    attributable (#521). -/
def signerAmbient : Signer := fun L a g i t => a.gpgsign && holdsClaim L g i t

/-! ## The properties, as predicates over signers -/

/-- **Soundness.** No signature without a live, issuer-attested claim on
    *this* issue at *this* time. -/
def Sound (S : Signer) : Prop :=
  ∀ L a g i t, S L a g i t = true → holdsClaim L g i t = true

/-- **Ambient-blindness.** Local state can neither confer signing nor
    withhold it. Both directions matter: #521's fault was ambient state
    silently switching a privileged effect *off*, and a self-asserted claim
    is ambient state switching it *on*. A capability that mutable local
    state can toggle either way is not a capability, it is a setting. -/
def AmbientBlind (S : Signer) : Prop :=
  ∀ L a₁ a₂ g i t, S L a₁ g i t = S L a₂ g i t

/-! ## A list lemma, proved rather than imported (no mathlib) -/

theorem any_eq_false {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x, x ∈ l → p x = false) : l.any p = false := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.any_cons, h a (List.Mem.head as), ih (fun x hx => h x (List.Mem.tail a hx))]
    rfl

/-! ## Theorem 1 — soundness -/

/-- **The headline biconditional.** A guest can sign issue `i` at `t` iff an
    issuer-attested claim binds it to `i` and is live at `t`.

    It is `Iff.rfl` — and that is the honest outcome, not a weak one. The
    content of this theorem is that `signerCorrect` is *defined* as the
    claim check and nothing else; the work of showing the property has teeth
    is done by the counterexamples below, which are the signers for which the
    corresponding statement is false. -/
theorem canSign_iff_holdsClaim (L : Ledger) (a : Ambient) (g : Guest) (i : Issue) (t : Time) :
    signerCorrect L a g i t = true ↔ holdsClaim L g i t = true := Iff.rfl

theorem signerCorrect_sound : Sound signerCorrect := fun _ _ _ _ _ h => h

/-! ## Theorem 2 — release revokes

Formally a contrapositive of soundness, stated separately because it is the
*operational* property and the one an implementation violates by checking
the claim at mint time only. -/

theorem live_false_of_released (c : Claim) (r t : Time)
    (h : c.release = some r) (hle : r ≤ t) : c.live t = false := by
  simp [Claim.live, h, Nat.not_lt.mpr hle]

/-- **Release revokes.** If every ledger claim binding `g` to `i` was
    released at or before `t`, then `g` cannot sign `i` at `t`.

    The quantification over `t` is the teeth: this is false for any signer
    that resolves liveness once, at mint time, and reuses the answer. It is
    the formal shape of "credentials mint per-push with a fresh claim check
    rather than per-claim." -/
theorem released_revokes (L : Ledger) (a : Ambient) (g : Guest) (i : Issue) (t : Time)
    (hrel : ∀ c, c ∈ L.claims → c.guest = g → c.issue = i →
      ∃ r, c.release = some r ∧ r ≤ t) :
    signerCorrect L a g i t = false := by
  show holdsClaim L g i t = false
  refine any_eq_false _ _ (fun c hc => ?_)
  by_cases hg : c.guest = g
  · by_cases hi : c.issue = i
    · obtain ⟨r, hr, hle⟩ := hrel c hc hg hi
      simp [Claim.binds, live_false_of_released c r t hr hle]
    · simp [Claim.binds, hi]
  · simp [Claim.binds, hg]

/-! ## Theorem 3 — no amplification across claims

Holding a claim on `i` must not confer signing for `j`. Stated as: a ledger
whose every claim is on `i` confers nothing on any other issue — including,
crucially, a different issue *in the same repo*, which is the case a
repo-scoped credential gets wrong. -/

theorem no_amplification (L : Ledger) (a : Ambient) (g : Guest) (i j : Issue) (t : Time)
    (hij : i ≠ j) (honly : ∀ c, c ∈ L.claims → c.issue = i) :
    signerCorrect L a g j t = false := by
  show holdsClaim L g j t = false
  refine any_eq_false _ _ (fun c hc => ?_)
  have : c.issue ≠ j := fun h => hij ((honly c hc).symm.trans h)
  simp [Claim.binds, this]

/-! ## Theorem 4 — the claim is issuer-attested

`holdsClaim` has no guest-side introduction rule. `GuestStep` enumerates
what a guest can do unaided and contains no constructor that writes the
ledger; these theorems are what make that absence checkable rather than
something someone remembers. -/

theorem run_ledger (w : World) (ss : List GuestStep) : (w.run ss).ledger = w.ledger := by
  induction ss generalizing w with
  | nil => rfl
  | cons s ss ih => exact ih (w.step s)

/-- **Issuer-attested.** No sequence of guest actions changes what the
    ledger says about any guest, issue, or time. -/
theorem holdsClaim_guest_invariant (w : World) (ss : List GuestStep)
    (g : Guest) (i : Issue) (t : Time) :
    holdsClaim (w.run ss).ledger g i t = holdsClaim w.ledger g i t := by
  rw [run_ledger]

/-- **No guest escalation** — the capstone, and the property the org
    actually wants. A guest that does not hold a live claim cannot obtain
    one by acting: not by rewriting its git config, not by presenting a
    claim record it wrote itself, not by any sequence of the two. -/
theorem no_guest_escalation (w : World) (ss : List GuestStep)
    (g : Guest) (i : Issue) (t : Time)
    (hno : holdsClaim w.ledger g i t = false) :
    signerCorrect (w.run ss).ledger (w.run ss).ambient g i t = false := by
  show holdsClaim (w.run ss).ledger g i t = false
  rw [run_ledger]; exact hno

/-! ## Theorem 5 — ambient state cannot confer signing -/

/-- **Ambient-blindness.** `signerCorrect` ignores local configuration
    entirely: signing is derivable only from the ledger. -/
theorem signerCorrect_ambientBlind : AmbientBlind signerCorrect :=
  fun _ _ _ _ _ _ => rfl


/-! ## Fixtures

The counterexamples below are not invented shapes — each reproduces a
configuration the org has actually been in. Following the `check-sync.mjs`
precedent, the facts they rest on are cited here rather than left implicit,
so a reader can check the model against the incident:

- **`prx#280` / `prx#1061`** — the issue claimed during the 2026-08-16
  session and a second issue in the same repo. Throughout that session the
  claim on `prx#280` was correct, live, and completely disconnected from
  the signature; the session could have signed work it never claimed.
- **release at `t = 10`** — #435, a `claimed` label left in place after work
  stopped. Harmless while claims grant nothing; a standing grant the moment
  they grant signing.
- **`gpgsign := false`** — #521, the repo-local `commit.gpgsign` line that
  silently decided whether a privileged effect was attributable (`prx#1060`,
  commit `a418775`: all 15 CI checks green, merge blocked on signatures).

These are fixtures of the **model**. They are drawn from real incidents;
they are not a measurement of any deployed signer. -/

/-- The guest in every fixture. -/
def fxGuest : Guest := ⟨1⟩

/-- `prx#280` — claimed, live, during the 2026-08-16 session. -/
def fxIssue280 : Issue := { repo := 7, num := 280 }

/-- `prx#1061` — a *different* issue in the *same* repo. Same-repo is the
    whole point: it is the case a repo-scoped credential gets wrong and an
    issue-scoped one gets right. -/
def fxIssue1061 : Issue := { repo := 7, num := 1061 }

/-- A claim opened at `0`, released at `10` (#435). -/
def fxReleased : Claim :=
  { guest := fxGuest, issue := fxIssue280, since := 0, release := some 10 }

/-- A live claim on `prx#280`, never released. -/
def fxLive : Claim :=
  { guest := fxGuest, issue := fxIssue280, since := 0, release := none }

def fxLedgerReleased : Ledger := ⟨[fxReleased]⟩
def fxLedgerLive : Ledger := ⟨[fxLive]⟩
def fxLedgerEmpty : Ledger := ⟨[]⟩

/-- A guest that wrote itself a claim record it does not hold. -/
def fxSelfAsserted : Ambient := { gpgsign := true, asserted := [fxLive] }

/-! ## The counterexamples

Each is closed by kernel `decide` — no `sorry`, no `native_decide`. -/

/-- #435. At `t = 20` the claim was released ten ticks ago, and
    `signerEverClaimed` signs anyway: a stale label is a standing grant. -/
theorem signerEverClaimed_unsound : ¬ Sound signerEverClaimed := fun h =>
  absurd (h fxLedgerReleased Ambient.stock fxGuest fxIssue280 20 (by decide)) (by decide)

/-- `signerCorrect` refuses the same request. The properties separate the
    two signers; this is what makes theorem 2 more than a restatement. -/
theorem signerCorrect_refuses_released :
    signerCorrect fxLedgerReleased Ambient.stock fxGuest fxIssue280 20 = false := by decide

/-- A repo-scoped credential signs for an issue that was never claimed. -/
theorem signerRepoScoped_unsound : ¬ Sound signerRepoScoped := fun h =>
  absurd (h fxLedgerLive Ambient.stock fxGuest fxIssue1061 5 (by decide)) (by decide)

theorem signerCorrect_refuses_other_issue :
    signerCorrect fxLedgerLive Ambient.stock fxGuest fxIssue1061 5 = false := by decide

/-- A guest-presented claim record confers signing against an empty ledger —
    the privilege escalation waiting behind `claim-ticket.yml` being a
    `workflow_dispatch` anyone can call. -/
theorem signerSelfAsserted_unsound : ¬ Sound signerSelfAsserted := fun h =>
  absurd (h fxLedgerEmpty fxSelfAsserted fxGuest fxIssue280 5 (by decide)) (by decide)

theorem signerCorrect_refuses_selfAsserted :
    signerCorrect fxLedgerEmpty fxSelfAsserted fxGuest fxIssue280 5 = false := by decide

/-- #521, in the model: flipping one local config line changes whether the
    effect happens, with the ledger untouched. -/
theorem signerAmbient_not_ambientBlind : ¬ AmbientBlind signerAmbient := fun h =>
  absurd (h fxLedgerLive { gpgsign := true, asserted := [] }
            { gpgsign := false, asserted := [] } fxGuest fxIssue280 5) (by decide)

/-- The other direction: ambient state switching signing *on*. -/
theorem signerSelfAsserted_not_ambientBlind : ¬ AmbientBlind signerSelfAsserted := fun h =>
  absurd (h fxLedgerEmpty Ambient.stock fxSelfAsserted fxGuest fxIssue280 5) (by decide)

/-! ## The model as the executable checker

The reason to prefer `Bool` throughout. `holdsClaim` is the predicate the
theorems above quantify over *and* a function that runs — so the checker a
signer consults and the checker that was proved sound can be one artifact
from one source, rather than two implementations that agree until they
don't. -/

-- Live claim, own issue → sign.
#guard signerCorrect fxLedgerLive Ambient.stock fxGuest fxIssue280 5 = true
-- Same claim, different issue in the same repo → refuse (theorem 3).
#guard signerCorrect fxLedgerLive Ambient.stock fxGuest fxIssue1061 5 = false
-- Before release → sign; at and after release → refuse (theorem 2).
#guard signerCorrect fxLedgerReleased Ambient.stock fxGuest fxIssue280 9 = true
#guard signerCorrect fxLedgerReleased Ambient.stock fxGuest fxIssue280 10 = false
-- Self-asserted claim, empty ledger → refuse (theorem 4).
#guard signerCorrect fxLedgerEmpty fxSelfAsserted fxGuest fxIssue280 5 = false

end Keycard
