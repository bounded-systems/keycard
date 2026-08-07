# keycard

**The OIDC model as machine-checked proofs, a hardened little tool, and a
standing question.**

A keycard is what the front desk issues a guest: short-lived, scoped, opens
specific doors, worthless once it expires. That is an OIDC token — issued by
an identity provider (the front desk), presented to a relying party's trust
policy (the door's reader), valid for one job, never a stored secret. This
repo is where the mechanism itself is modeled, proved, and explained — not
where any credential is held. The room has no privileged door: public repo,
standard hardening, no secrets.

## Claim boundary — read this before reading the proofs

Every theorem in `Keycard/` is a property of the **model** in
`Keycard/Model.lean` — small discrete structures standing in for issuers,
names, principals, and trust policies. **Nothing here sits in an enforcement
path, and no theorem certifies a deployment.** Whether a real issuer or a
real relying party matches the model is a separate, labeled, empirical
claim, made elsewhere or not at all. A green `lake build` means the theorems
hold *of the model* — it must never be read, or quoted, as "the deployment
is proved safe."

## What OIDC asserts — and what it doesn't

An OIDC token asserts **where and as what something ran** — the execution
context, pinned at issuance. It does not assert *what it could do* (that's
the capability grant the relying party attaches — the door), *how it was
built* (that's in-toto/SLSA provenance, an attestation *signed by* the OIDC
identity, not contained in it), or *whether it was authorized* (that's a
gate — a predicate over the change, checked separately). OIDC is the anchor
claim the other three build on, which is why pinning the subject down
immutably is worth real machinery: every downstream statement inherits the
anchor's integrity.

## The seed arc (`Keycard/`)

One sentence of OpenID Connect Core — a subject is *"locally unique and
never reassigned"* — carries the whole first arc:

| File | What it proves |
|---|---|
| `Model.lean` | The structures: names (recyclable), principals (not), issuance contexts, subject schemes, and `NeverReassigned` — the invariant every sub-matching relying party silently assumes. |
| `Recycling.lean` | **Counterexample.** Name-based subjects (the pre-2026 GitHub format) violate the invariant under name recycling: same `sub`, two principals. |
| `Soundness.lean` | **Soundness.** Subjects embedding an immutable ID satisfy the invariant in *every* world, conditional on exactly one explicit assumption: the issuer never reassigns IDs. |
| `Matcher.lean` | **Relying parties.** Sub-only matchers are sound iff the sub embeds the ID; claim-matchers recover soundness under mutable subs by pinning `repository_id`; and the `repo:ORG/*` wildcard corollary — the pattern silently stops matching after the immutable flip — proved on the actual strings, kernel-checked. |

No mathlib, no `sorry`, no `native_decide`: core Lean, kernel-checked, and
`lake build` failing *is* the red check — theorems are self-certifying.

## The tool (`tools/`)

One hardened Rust binary, `keycard`, Linux-first. Two subcommands:

- `keycard decode` — prints a JWT's header and claims for inspection.
  Decode, **not** verify. **The raw token never reaches any output stream**
  — a live OIDC token in a CI log is a replayable credential, so errors
  describe shape, never content.
- `keycard lint` — flags trust-policy subject patterns that trust labels
  instead of identities: mutable-name matchers, `repo:ORG/*` wildcards
  missing `@ID`, unbounded wildcards. The rules are the theorems'
  deployment shadow; exit 1 on errors.

Posture: no network, ever, in this version (a future JWKS fetch would be an
explicit opt-in flag); one dependency (`serde_json`); base64url and argument
parsing hand-rolled — every dependency is attack surface in a tool people
point at credentials.

## The standing question (`docs/rubric.md`)

> **Does OIDC apply here?** — asked wherever a credential crosses a
> boundary.

Four checks; each "yes" strengthens the case for federation over a stored
secret. `docs/keycards.md` is the prose explainer.

## Building

```sh
lake build                                  # the proofs (toolchain pinned in lean-toolchain)
cargo test --manifest-path tools/Cargo.toml # the tool
```

CI note: elan's installer talks to `elan.lean-lang.org` and the toolchain
downloads come from `releases.lean-lang.org` (plural — verified against a
live build; docs elsewhere say `release.`, singular). An egress allowlist
must admit what a build actually requests.

## License

[PolyForm Noncommercial 1.0.0](./LICENSE).
