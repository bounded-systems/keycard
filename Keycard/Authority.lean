import Keycard.Model
/-!
# Degrading authority: the model

The structures behind one sentence:

> When the authority a policy named is revoked, the operation must
> **refuse** — not proceed under a weaker principal that happens to be
> lying around.

This is the same shape as `Claim.lean` and `Transcript.lean`, one boundary
over again. There the questions were what may confer *signing* and what may
confer *disclosure*. Here the question is narrower and nastier: given that
authority has been correctly withdrawn, what may **silently supply a
replacement** — and can the caller tell.

## Why this is a fourth failure mode and not one of the first three

The existing arcs cover self-assertion (`signerSelfAsserted`), revocation
(`released_revokes`) and amplification (`no_amplification`). Degradation is
adjacent to all three and is none of them:

- the principal is **not lying about itself** — the fallback is a genuine,
  issuer-minted identity presenting its own true capabilities;
- the credential **is** correctly revoked — the revocation works, and the
  keyring says so;
- **no authority is amplified** — the substitute is strictly *weaker*.

Authority is *reduced*, and the reduction is invisible at the call site.
None of the first three properties is violated, and the operation still
does the wrong thing.

## What the caller sees is part of the model

`Report` exists because this failure mode is defined by an observation that
did not happen. A run that writes nothing and exits green is not
distinguishable, by its caller, from a run that did the work. So the outcome
carries what the caller sees alongside what actually happened, and the
properties in `Degradation.lean` relate the two. A model with no `Report`
can state "the wrong principal acted" but cannot state "and nobody could
tell", which is the whole defect.

## Why `Bool`, and why grants are a list

Every predicate lands in `Bool`, for `Claim.lean`'s reason: the checker and
the theorems should be one artifact rather than two implementations that
agree until they don't.

The capability order is **grant-set inclusion** — `a` is weaker than `b`
when every grant `a` carries, `b` carries too. That is all the lattice
structure any property below needs, so it is all that is built; meets and
joins would be set intersection and union and nothing here asks for them.
Grants are an explicit `List` rather than a predicate so that the order is
decidable and every counterexample closes by kernel `decide`.

Everything here is a property of *this model*. That any deployed workflow
refuses correctly is a separate, labeled claim — see the README.
-/

namespace Keycard.Degradation

/-! ## Repositories, actions, grants -/

/-- A repository — the target of an operation. `isPrivate` is carried
    because the incident's second consequence is stated in terms of it: the
    enumeration did not fail, it silently *narrowed to the public repos*. A
    model that cannot say which repos dropped out cannot state that. -/
structure Repo where
  id        : Nat
  isPrivate : Bool
deriving DecidableEq, Repr

/-- What an operation does to a repo. Both cases are drawn from the
    incident: `write` is the cross-repo catalog write, `read` is the org
    enumeration. -/
inductive Action where
  | read
  | write
deriving DecidableEq, Repr

/-- One capability — one door. A grant is an (action, repo) pair rather
    than a bare scope string, so that "read everything, write nothing"
    — which is exactly what the fallback principal carries — is
    representable. -/
structure Grant where
  action : Action
  repo   : Repo
deriving DecidableEq, Repr

/-! ## Authorities and the capability order -/

/-- A principal together with the capability set it carries. `id` is the
    identity the effect is attributable to; `grants` is what it can do.
    Keeping both in one structure is deliberate: the defect being modeled
    is precisely a change of `id` that travels with a change of `grants`,
    and a model that separated them could not state that they moved
    together. -/
structure Authority where
  id     : Nat
  grants : List Grant
deriving DecidableEq, Repr

/-- Does this authority carry this capability? -/
def Authority.permits (a : Authority) (g : Grant) : Bool :=
  a.grants.any (fun x => decide (x = g))

/-- **The capability order: grant-set inclusion.** `a` is weaker than `b`
    when `b` carries every grant `a` does. -/
def Authority.weakerThan (a b : Authority) : Bool :=
  a.grants.all (fun g => b.permits g)

/-- Strictly weaker — weaker, and not equally strong. This is the
    relation the incident's fallback stands in to the credential it
    replaced, and it is checked of the fixtures rather than asserted in a
    comment. -/
def Authority.strictlyWeakerThan (a b : Authority) : Bool :=
  a.weakerThan b && !b.weakerThan a

/-! ## Revocation

The issuer's record of what it has withdrawn. Revocation is modeled as the
issuer's act, not the holder's: a credential audit revokes a token, and no
sequence of things the workflow does puts it back. -/

/-- The issuer's revocation record. `revoked` holds the authority ids the
    issuer has withdrawn — a credential audit is an insertion here. -/
structure Keyring where
  revoked : List Nat
deriving Repr

/-- Is this authority still usable? -/
def Keyring.live (k : Keyring) (a : Authority) : Bool :=
  !k.revoked.any (fun n => decide (n = a.id))

/-! ## Operations and outcomes -/

/-- An operation the policy wants performed: one action, over a set of
    target repos. The incident's two operations are exactly this shape —
    write the catalog to every repo in the org, and enumerate every repo in
    the org. -/
structure Operation where
  action  : Action
  targets : List Repo
deriving DecidableEq, Repr

/-- The targets an authority can actually reach. This is the *narrowing*:
    under a weaker authority the same operation over the same targets
    touches a subset, and the subset is what a partial artifact gets built
    from. -/
def Operation.reached (op : Operation) (a : Authority) : List Repo :=
  op.targets.filter (fun r => a.permits { action := op.action, repo := r })

/-- Does this authority cover the whole operation? -/
def Operation.covered (op : Operation) (a : Authority) : Bool :=
  op.targets.all (fun r => a.permits { action := op.action, repo := r })

/-- What the caller observes — and nothing more. The four content-catalog
    workflows exited `success`; that is the entire signal downstream had to
    work with, and it is why the defect went unnoticed. -/
inductive Report where
  | success
  | refused
deriving DecidableEq, Repr

/-- What happened: the authority the effect is attributable to, the targets
    actually touched, and what the caller was told. The gap between the
    second and the third field is the failure mode. -/
structure Outcome where
  under   : Authority
  reached : List Repo
  report  : Report
deriving DecidableEq, Repr

end Keycard.Degradation
