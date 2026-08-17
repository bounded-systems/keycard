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

### Claim-bound signing, specifically

The second arc proves that a guest can sign issue `i` at time `t` **iff** an
issuer-attested claim binds it to `i` and is live at `t`. That sentence has
an obvious wrong reading, so it is closed here rather than left to the
reader to close for themselves:

> **"We proved claim-bound signing" does not mean any deployed signer
> refuses correctly.**

It means the *rules* are coherent, non-circular, and free of the revocation,
amplification, and self-assertion bugs the counterexamples in
`Signing.lean` exhibit. No signer in this org consults these definitions
today, and nothing in this repo has ever observed a real signature. Whether
an implementation conforms to the model is a separate claim needing its own
evidence — the "Lean conformance theorems" thread, which lives elsewhere.

The fixtures in `Signing.lean` are drawn from real incidents and cite them.
They are cited so the model can be checked *against* what happened — not
because evaluating them measures anything about a live system. A `#guard`
here is a statement about `Keycard.holdsClaim`, not about `keeperd`.

### Transcript disclosure, specifically

The fourth arc proves properties about when a session transcript may cross the
boundary to a third party. It has its own wrong reading, so it is closed here
too:

> **"We modelled disclosure" does not mean anything is prevented from
> uploading.**

Nothing in this org consults these definitions. The org's share step
(`.github-private` → `.claude/share-session.sh`) has never heard of them; it
is gated by an environment variable, and `policyEnvVar` in
`Keycard/Disclosure.lean` is that gate, proved **unsound** as authority. The
model names a defect in a shipped implementation; it does not repair it.

### Degrading authority, specifically

The fifth arc models a credential that, when revoked, is silently replaced by
a weaker one. Its wrong reading:

> **This models a defect; it does not fix one.**

The incident it is drawn from has since been repaired in the real system —
`bounded-systems/content-catalog#11` removed the `||` fallback, and
`content-catalog#13` replaced the credential outright with brokered,
per-workflow OIDC mints (`content-catalog#10`, closed). That repair happened
in YAML, with its own evidence, and **owes nothing to these theorems**.
Nothing in this org consults these definitions, and a green `lake build` here
would have said exactly as much on the day the bug was live. What this arc
establishes is that the failure mode has a name, that the two halves of it are
independent, and that three named strategies for "handling" a revoked
credential each fail in a stated way.

> This paragraph previously asserted that the four workflows "still read it
> that way", and that the incident was open. Both stopped being true between
> this arc being branched and merged. The correction is kept visible rather
> than silently rewritten, because a claim boundary that misstates the world
> is the exact failure this repo exists to prevent — and because arc 5 is
> itself about a fact that quietly stopped holding while something went on
> relying on it (`#13`).

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

## Claim-bound signing (`Keycard/Claim.lean`, `Keycard/Signing.lean`)

> A guest can produce a valid signature over a change to issue `i` at time
> `t` **iff** an issuer-attested claim binds that guest to `i` and is live
> at `t`.

The `iff` carries the weight. Soundness alone — "signing implies a claim" —
permits a system where the claim exists and signing works regardless, which
is precisely the state the convention is in when a claim grants nothing.

| Theorem | What it says |
|---|---|
| `canSign_iff_holdsClaim` | The headline biconditional. `Iff.rfl`: the signer is *defined* as the claim check and nothing else. |
| `signerCorrect_sound` | **Soundness.** No signature without a live, issuer-attested claim on *this* issue at *this* time. |
| `released_revokes` | **Release revokes.** Once every claim binding `g` to `i` is released at or before `t`, `g` cannot sign at `t`. Quantifying over `t` is what excludes a signer that resolves liveness once, at mint time. |
| `no_amplification` | **Attenuation.** A ledger whose every claim is on `i` confers nothing on any other issue — including a different issue in the *same repo*. |
| `holdsClaim_guest_invariant` | **Issuer-attested.** No sequence of guest actions changes what the ledger says. `SessionStep` has no constructor that writes it; this theorem is what makes that absence checkable. |
| `no_guest_escalation` | The capstone. A guest without a live claim cannot obtain one by acting — not by rewriting local config, not by presenting a claim record it wrote itself, not by any sequence of the two. |
| `signerCorrect_ambientBlind` | **Ambient state confers nothing.** Local configuration can neither switch signing on nor switch it off. |

### Why these are not vacuous

A property proved only of the implementation that satisfies it by
construction proves nothing about the property. So each theorem is stated
over an abstract `Signer`, and each is paired with a **named signer that
violates it**, closed by kernel `decide`. Every broken signer is a real
implementation strategy:

| Broken signer | The mistake | Violates |
|---|---|---|
| `signerEverClaimed` | checks the claim exists, never that it is *live* | soundness |
| `signerRepoScoped` | mints a repo-scoped credential instead of an issue-scoped one | soundness, at a second issue |
| `signerSelfAsserted` | trusts a claim record the guest presented about itself | soundness, ambient-blindness |
| `signerAmbient` | lets local git config decide whether the effect is attributable | ambient-blindness |

That the properties *separate* these signers is the evidence that they have
content. Each broken signer is accompanied by a theorem that `signerCorrect`
refuses the same request.

### Model and checker from one source

Every predicate lands in `Bool` rather than `Prop`. That is the design bet:
for claim-bound signing the executable checker **is** the runtime gate, so
the predicate a signer runs to decide sign-or-refuse and the predicate the
theorems quantify over should be one artifact, not two implementations that
agree until they don't. `holdsClaim` runs; the `#guard` lines at the foot of
`Signing.lean` are checked by `lake build`.

## Transcript disclosure (`Keycard/Transcript.lean`, `Keycard/Disclosure.lean`, `specs/tla/`)

> When may a session transcript cross the boundary to a third party, and
> under whose identity?

A transcript is not a diff. It carries the conversation, the tool calls and
the dead ends, so it can carry secrets, tokens, internal hostnames and the
contents of private repositories. That makes an upload a **privileged
effect** — the same shape as signing, one boundary over — and the arc asks
what may confer it.

Two results answer questions that were open in prose:

| Theorem | What it settles |
|---|---|
| `unlisted_published_is_public` | "Unlisted" is **not** a privacy property. Once the URL is posted on a public pull request the audience is everyone; the vendor's server-side setting and the org's publishing decision compose, and the composition is public. |
| `anon_refused_under_any_decision` | The anonymous endpoint is refused under **every** decision an owner could write, including the most permissive. It is not a policy question: an anonymous upload has no owner, so no account exists from which to delete it. |

The second is why the safe default is not "share less" but "share nothing
until an account we control is on the other end".

### Why these are not vacuous

Same discipline as the signing arc — every property stated over an abstract
`Policy`, every one paired with a named policy that violates it, closed by
kernel `decide`. Three of the four broken policies are running or proposed
right now:

| Broken policy | The mistake | Violates |
|---|---|---|
| `policyBareShare` | uploads with whatever auth it has, falling back to anonymous | revocability, decision-grounding |
| `policyEnvVar` | an environment variable decides disclosure | ambient-blindness, decision-grounding |
| `policyUnlistedIsEnough` | unlisted treated as sufficient for private content | private-guarding, redaction |
| `policyFailOpen` | absence of a decision read as permission | decision-grounding |

`policyEnvVar` is **the org's own share step**, and the pair of results about
it is the point of the arc: it is `Revocable` — the `--name` guard against
the anonymous fallback genuinely holds — and it is *not* `EnvBlind`. One
`export` moves the disclosure decision. That is #521's `commit.gpgsign` fault
at a different boundary: authority that mutable local state can toggle is not
authority, it is a setting.

### The temporal half (`specs/tla/`)

The Lean theorems quantify over a decision record; they cannot see that
`path share` reads the decision at preflight and acts on it after the derive.
`specs/tla/disclosure.tla` splits every check-then-act across two actions and
lets TLC find the interleaving. Three configs, and the middle one carries the
result: **the TOCTOU and the anonymous fallback are independent faults, and
neither fix closes the other.** See `specs/tla/README.md`.

## Degrading authority (`Keycard/Authority.lean`, `Keycard/Degradation.lean`, `specs/tla/degradation.tla`)

> When the authority a policy named is revoked, does the operation refuse —
> or proceed under a weaker principal that happens to be lying around?

```yaml
GITHUB_TOKEN: ${{ secrets.BOOTSTRAP_TOKEN || secrets.GITHUB_TOKEN }}
```

A 2026-08-16 credential audit revoked the PAT behind `secrets.BOOTSTRAP_TOKEN`
in `bounded-systems/content-catalog`, where four workflows read it that way.
The `||` did not fail. It resolved to the next term — repo-scoped and
read-only by org default — so revocation did not close the door, it
**substituted a weaker principal and reported success**. Two consequences, both
green: the cross-repo write visited every repo and wrote nothing, and the org
enumeration narrowed to public repos only, shipping a partial catalog that is
committed *and* SLSA-attested.

This is a fourth failure mode, not a restatement of the first three. The
principal is not lying about itself (`signerSelfAsserted`), the credential
*is* correctly revoked (`released_revokes`), and no authority is amplified
(`no_amplification`). Authority is **reduced**, and the reduction is invisible
at the call site.

| Theorem | What it says |
|---|---|
| `degradation_is_unobservable` | Under the shipped `||`, the report is identical whether or not the credential was revoked. This is the formal content of the word "silently" — and it is `rfl`, because that runner cannot produce any other report. |
| `degradation_changes_effects` | …while the set of repos actually touched is not identical. Same signal, different world: that pair is the incident. |
| `revoked_refuses_under_any_fallback` | The correct runner refuses a revoked authority under **every** fallback the environment could supply — including one that would cover the operation outright. A revocation the caller can route around is not a revocation. |
| `fallback_enumeration_is_public_only` | The narrowing, on the fixtures: every repo the degraded enumeration reached is public. The private ones left the catalog without anything failing. |
| `fxGithubToken_strictly_weaker` | The premise, checked rather than asserted: the substitute carries a strict subset of the grants. |

### Why these are not vacuous

Same discipline: every property stated over an abstract `Runner`, every one
paired with a named runner that violates it, closed by kernel `decide`.

| Broken runner | The mistake | Violates |
|---|---|---|
| `runnerFallback` | `A \|\| B` — revocation resolves to the next term | all four |
| `runnerBestEffort` | loops the targets, greens on whatever it reached | `Faithful` only |
| `runnerSufficientFallback` | substitutes, but only when the substitute suffices | all but `Faithful` |

The last two rows are load-bearing: they violate **disjoint** sets of
properties. That is what shows `Faithful` and `ActsAsNamed` are independent
rather than two spellings of one idea — reporting failures honestly does not
make the effects attributable to the right principal, and removing the `||`
does not stop a truncated run from shipping green.

`FallbackBlind` is `AmbientBlind` (`Signing.lean`) and `EnvBlind`
(`Disclosure.lean`) at a third boundary, and the sentence is the same one:
authority that ambient state can supply is not authority, it is a setting.
`secrets.GITHUB_TOKEN` is ambient in the strictest sense — nobody puts it
there, which is what makes `||` so easy to write and so hard to notice.

### The temporal half

The Lean theorems cannot see that the run is not one step: the credential is
selected when the expression is evaluated and used over the minutes that
follow, one target at a time. So revocation has two places to land — before
selection, causing substitution, and mid-run, truncating work already under
way. `specs/tla/degradation.tla` splits `Select` from `Visit` and lets TLC
find both. Four configs; the middle two carry the result, exhibiting the same
independence in both directions, and they are checked under TLC's `-continue`
so that "the other invariant holds" is a statement about the whole state space
rather than about where the search stopped.

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
bash specs/tla/check.sh                     # the TLC model check (needs java)
```

CI note: elan's installer talks to `elan.lean-lang.org` and the toolchain
downloads come from `releases.lean-lang.org` (plural — verified against a
live build; docs elsewhere say `release.`, singular). An egress allowlist
must admit what a build actually requests.

## License

[PolyForm Noncommercial 1.0.0](./LICENSE).
