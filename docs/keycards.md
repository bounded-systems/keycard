# Keycards

*The explainer behind <https://github.com/bounded-systems/keycard> — written
for the org site. Hotel voice throughout, because the Hotel is the org's
naming system: rooms are processes, doors are capability sets, and the front
desk issues the keycards.*

## A keycard is not a skeleton key

When you check in, the front desk does not hand you a master key and a
promise that you seem trustworthy. It hands you a keycard: it opens your
room, the gym, maybe the pool — for the length of your stay, and then it is
plastic. Short-lived, scoped, per-door.

An OIDC token is that keycard. A workload — a CI job, a room on some floor —
checks in with the identity provider, which mints a token recording *where
and as what the workload is running*: repository, workflow, ref,
environment. The token expires in minutes. It is useless at doors it was
never scoped for. And crucially, nobody had to hide a master key under the
mat: there is no long-lived secret sitting in a settings page waiting to be
stolen.

## The front desk and the door reader never share a secret

The magic of the keycard system is what it *removes*. The door reader does
not phone the front desk to ask "did you issue this?" — and neither do they
share a password. The reader checks two things: the card's signature (only
the front desk can mint one) and its claims (this room, this guest, these
dates). The issuer publishes a public key; the relying party verifies
against it. That's federation: trust without a shared secret, which means
nothing to leak, rotate, or forget in a config page from 2023.

## The room-number problem

Here is where it gets interesting — and where this repo stops explaining and
starts proving.

Suppose keycards name rooms by their *label*: "Suite acme/widget." Labels
get reused. The guest in acme/widget checks out; the label returns to the
pool; a new guest takes the room. If the door reader trusts the label,
yesterday's guest opens today's room — the card says "Suite acme/widget" and
so does the door.

That is not a hypothetical. GitHub's original OIDC subject format built the
`sub` from names — `repo:OWNER/REPO:...` — and GitHub names are recyclable:
delete or rename an account and the label frees up. The OpenID Connect spec
demands subjects be "locally unique and **never reassigned**," and a
name-based subject under recycling breaks that in exactly the yesterday's-
guest way. `Keycard/Recycling.lean` exhibits the violation as a
machine-checked counterexample; `Keycard/Soundness.lean` proves the fix —
embed an immutable ID next to the name (`acme@7241/widget@90513`) and the
invariant holds in every world, recycling or not, on one explicit
assumption: the front desk never reissues an ID.

There's a sting in the tail for existing policies:
`Keycard/Matcher.lean` proves that a `repo:acme/*` wildcard written against
the old format *silently stops matching* once subjects flip to the new one —
`acme@7241` is not `acme`. It fails closed, but a policy that combined
several patterns is now trusting whichever arm still matches. The `keycard
lint` tool flags exactly these patterns, because the theorems say exactly
these patterns are the trap.

## Ask at every seam: does OIDC apply here?

The org asks one standing question wherever a credential crosses a
boundary: **does OIDC apply here?** Is there a workload identity? Is a
long-lived secret standing in for it? Can the relying party verify claims?
Is the subject immutable? Four yeses and the stored secret should probably
be a keycard instead. The rubric, and the plan to make it a mechanical
audit rather than a habit, live in [rubric.md](./rubric.md).

## What we proved

Everything above that sounds like a theorem *is* one, checked by the Lean
kernel on every commit — the build failing is the red check. And one
boundary, stated as often as it takes: the theorems are properties of a
small model, not certifications of any deployment. The model is honest
about what it captures; whether the world matches it is a separate claim,
labeled as such. Start at `Keycard/Model.lean` and read the arc in order —
it is four short files, and the counterexample is the fun one.
