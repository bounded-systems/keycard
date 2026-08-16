import Keycard.Model
/-!
# Claim-bound signing: the model

The structures behind one sentence:

> A guest can produce a valid signature over a change to issue `i` at time
> `t` **iff** an issuer-attested claim binds that guest to `i` and is live
> at `t`.

Everything here is a property of **this model**. That a deployment matches
it is a separate, labeled claim — see the claim-boundary statement in the
README. Nothing in this file gates anything.

## Why `Bool` and not `Prop`

Every predicate below lands in `Bool`, not `Prop`. That is deliberate and
it is the whole design bet: for claim-bound signing the executable checker
**is** the runtime gate, so the predicate a signer runs to decide
sign-or-refuse and the predicate the theorems quantify over should be one
artifact from one source. `holdsClaim` is `#eval`-able (see `Signing.lean`)
and every counterexample below is closed by kernel `decide`.

Identifiers are `Nat`, not `String`, for a recorded reason: `Recycling.lean`
and `Matcher.lean` had to hand-roll a `List Char` prefix because
`String.isPrefixOf` does not kernel-reduce. Nothing here needs string
structure, so nothing here pays that cost.
-/

namespace Keycard

/-- A guest — an agent. Distinct from `Principal` (`Model.lean`) on purpose:
    a `Principal` is who an OIDC token speaks for, a `Guest` is who holds a
    Front Desk claim. Binding the two is #520's question, and none of the
    theorems in this file depend on how it is answered. -/
structure Guest where
  id : Nat
deriving DecidableEq, Repr

/-- A unit of work. The `repo` field exists so that issue-scoped and
    repo-scoped credentials are *distinguishable in the model* — without it
    the amplification theorem could not state the bug it exists to exclude. -/
structure Issue where
  repo : Nat
  num  : Nat
deriving DecidableEq, Repr

/-- An issuer-written claim record: this guest holds this issue over this
    interval. `release = none` means "not yet released"; `some r` means the
    claim stopped being live at `r`.

    Time is explicit rather than implicit because the operational failure
    (#435) is entirely temporal: a claim that was live when a credential was
    minted and is not live when it is used. A model with no `t` cannot state
    the difference. -/
structure Claim where
  guest   : Guest
  issue   : Issue
  since   : Time
  release : Option Time
deriving DecidableEq, Repr

/-- Liveness at an instant: begun, and not yet released. -/
def Claim.live (c : Claim) (t : Time) : Bool :=
  decide (c.since ≤ t) &&
    (match c.release with
     | none   => true
     | some r => decide (t < r))

/-- The issuer's claim ledger — the Front Desk's record. **Only the issuer
    writes it.** That is not enforced by a comment: `GuestStep` below has no
    constructor that touches it, and `holdsClaim_guest_invariant` is the
    proof that no sequence of guest actions can change what it says. -/
structure Ledger where
  claims : List Claim
deriving Repr

/-- Does this claim record bind `g` to `i`, live at `t`? -/
def Claim.binds (c : Claim) (g : Guest) (i : Issue) (t : Time) : Bool :=
  decide (c.guest = g) && decide (c.issue = i) && c.live t

/-- **The predicate.** Issuer-attested, issue-scoped, time-indexed. This is
    the executable checker; the theorems in `Signing.lean` are about it. -/
def holdsClaim (L : Ledger) (g : Guest) (i : Issue) (t : Time) : Bool :=
  L.claims.any (fun c => c.binds g i t)

/-! ## Guest-side authority

What a guest can do **on its own authority**. Read the constructors as an
exhaustive list: a guest may rewrite its ambient configuration and may
assert anything it likes about its own claims.

There is no constructor that writes the `Ledger`. That absence is
theorem 4, and `holdsClaim_guest_invariant` is what turns it from a fact
about this inductive type into a checkable property. -/

/-- Guest-mutable ambient state.

    `gpgsign` is the repo-local `commit.gpgsign` line from #521 — ordinary
    config, writable by anyone with a checkout. `asserted` is the
    guest-presented claim: today `claim-ticket.yml` is a `workflow_dispatch`
    any session can call, so a self-asserted claim record is a thing that
    can actually exist. -/
structure Ambient where
  gpgsign  : Bool
  asserted : List Claim
deriving Repr

/-- The ambient state of a session that has done nothing unusual. -/
def Ambient.stock : Ambient := { gpgsign := true, asserted := [] }

/-- Everything a guest can do without the issuer. Note what is absent. -/
inductive GuestStep where
  /-- Write repo-local `commit.gpgsign` (#521). -/
  | setGpgsign (b : Bool)
  /-- Present a self-asserted claim record. -/
  | assertClaim (c : Claim)
  /-- Drop presented assertions. -/
  | clearAssertions
deriving Repr

def GuestStep.apply (s : GuestStep) (a : Ambient) : Ambient :=
  match s with
  | .setGpgsign b   => { a with gpgsign := b }
  | .assertClaim c  => { a with asserted := c :: a.asserted }
  | .clearAssertions => { a with asserted := [] }

/-- A world: the issuer's ledger, plus the guest's ambient state. -/
structure World where
  ledger  : Ledger
  ambient : Ambient

def World.step (w : World) (s : GuestStep) : World :=
  { w with ambient := s.apply w.ambient }

/-- Run an arbitrary sequence of guest actions. -/
def World.run (w : World) : List GuestStep → World
  | []      => w
  | s :: ss => (w.step s).run ss

end Keycard
