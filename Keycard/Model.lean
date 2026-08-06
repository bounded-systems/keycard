/-!
# The model

Small discrete structures for one sentence of OpenID Connect Core §8:

> A `sub` (subject) — locally unique and **never reassigned** identifier
> within the Issuer for the End-User.

A *principal* is the entity a token should speak for. A *name* is a
recyclable label (an `owner/repo` path). The issuer authenticates a
principal holding a name at a moment in time — that moment is a `Ctx` —
and derives the token's subject from it via a `SubScheme`.

Everything a theorem in this repo says is a property of THIS model.
Whether a deployment matches the model is a separate, labeled claim
(see `claim-boundary` discipline in the README). Nothing here gates
anything.
-/

namespace Keycard

/-- The entity a token should speak for. Two `Principal`s with different
    `entity` fields are different entities, full stop — the model's ground
    truth, against which subject schemes are judged. -/
structure Principal where
  entity : Nat
deriving DecidableEq, Repr

/-- A recyclable label — an `owner/repo` path. Nothing stops two distinct
    principals holding the same `Name` at different times; that is the whole
    problem. -/
structure Name where
  raw : String
deriving DecidableEq, Repr

/-- Discrete time. -/
abbrev Time := Nat

/-- An ownership history: who holds a name at each instant (`none` =
    unclaimed). Name recycling is an `Ownership` under which the same name
    maps to different principals at different times. -/
def Ownership := Time → Name → Option Principal

/-- An issuance context: the moment a token is minted. The issuer has
    authenticated `principal` as the holder of `name` at time `t` — the
    context is what the issuer *knows*; the subject is what it *says*. -/
structure Ctx where
  t : Time
  name : Name
  principal : Principal
deriving DecidableEq, Repr

/-- A context is honest w.r.t. an ownership history if the principal really
    held the name at that time. Dishonest contexts model issuer compromise,
    which is out of scope for the subject-scheme theorems. -/
def Ctx.honest (w : Ownership) (c : Ctx) : Prop :=
  w c.t c.name = some c.principal

/-- A subject scheme: how the issuer derives the `sub` from what it knows.
    `α` is the subject's carrier — kept structured (not a string) so the
    theorems are about *information*, not parsing. String encodings and
    their delimiter discipline are `Matcher.lean`'s department. -/
def SubScheme (α : Type) := Ctx → α

/-- OIDC Core's "locally unique and never reassigned", stated over a world:
    across all honest issuances at *any* pair of times, equal subjects come
    from equal principals. This is the invariant every relying party
    silently assumes when it matches a `sub`. -/
def NeverReassigned {α : Type} (w : Ownership) (f : SubScheme α) : Prop :=
  ∀ c₁ c₂ : Ctx, c₁.honest w → c₂.honest w →
    f c₁ = f c₂ → c₁.principal = c₂.principal

end Keycard
