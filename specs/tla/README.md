# specs/tla — the temporal projections

Two specs, one discipline. Each is the temporal half of a Lean arc. The Lean
theorems quantify over a record — a decision, a revocation — and cannot see
that the real mechanism *reads* that record at one instant and *acts* on it at
a later one. So every check-then-act is split across two actions with a yield
point between, and TLC explores the interleavings a real run would hit — the
same shape as `front-desk-scheduler/specs/tla`, from which this borrows its
discipline.

| spec | Lean arc | the fault it exists for |
|---|---|---|
| `disclosure.tla` | `Keycard/Disclosure.lean` | consent read at preflight, acted on after the derive |
| `degradation.tla` | `Keycard/Authority.lean` | a revoked credential silently replaced by a weaker one |

## Running it

```sh
bash specs/tla/check.sh          # fetches the pinned tla2tools, verifies its digest
TLA2TOOLS=/path/to/tla2tools.jar bash specs/tla/check.sh   # or bring your own
```

The runner **asserts** each config's outcome rather than reporting it. Most of
the configs are supposed to fail; a runner that only printed TLC's output would
go green if a future edit quietly made a racy config pass, which is exactly the
case worth catching. A spec whose counterexamples have stopped reproducing has
stopped saying anything. This is the TLA+ half of the anti-vacuity discipline
the Lean side gets from its named counterexample policies.

---

## `disclosure.tla` — transcript disclosure

The Lean arc in `Keycard/Disclosure.lean` proves the pure-policy properties
for all inputs: given a decision record, a session and an upload, what may a
policy permit. Those theorems cannot see the fault this module exists for,
because the fault is temporal.

**`path share` does not decide and upload in one step.** It runs
`preflight_auth`, then derives the graph, then uploads. The decision that
authorises the upload is read at one instant and acted on at a later one,
with the expensive derive in between. Between them the owner can withdraw
consent and a credential can expire. Bytes already sent do not come back.

### The three configs

| config | `Atomic` | `AllowAnonFallback` | expected |
|---|---|---|---|
| `disclosure-racy.cfg` | FALSE | TRUE | `NoUnconsentedDisclosure` violated |
| `disclosure-anon.cfg` | **TRUE** | TRUE | `NoAnonUpload` violated, `NoUnconsentedDisclosure` **holds** |
| `disclosure-safe.cfg` | TRUE | FALSE | clean: every invariant, plus `Termination` |

#### Why there are three and not two

`disclosure-anon.cfg` is the one carrying the result. **The two faults are
independent**, and neither fix closes the other:

- Making the check atomic closes the TOCTOU. It does **not** stop a
  credential failure from downgrading to the anonymous endpoint.
- Forbidding the fallback closes the anonymous upload. It does **not** stop
  a stale consent read from authorising an upload.

With `Atomic = TRUE` and the fallback still live, TLC reports
`NoAnonUpload` violated while `NoUnconsentedDisclosure` holds — the
separation, exhibited rather than argued. The runner asserts both halves,
including that `NoUnconsentedDisclosure` keeps holding, so the config cannot
silently stop isolating what it was built to isolate.

### The invariants

- **`NoUnconsentedDisclosure`** — nothing was uploaded at an instant when
  the owner's decision said no. The temporal half of Lean's
  `DecisionGrounded`: that property quantifies over a decision record, this
  one over the moment of use.
- **`NoAnonUpload`** — nothing was uploaded anonymously. This *is* the
  retractability property: an anonymous upload has no owner, so no account
  exists from which to delete it. `anonPublished` is the set of things that
  can never be taken back, and the invariant is that it stays empty. Lean's
  counterpart is `anon_refused_under_any_decision`.
- **`Termination`** (safe config only) — fail-closed must not mean
  fail-*stuck*. Refusing is a decision the session reaches and reports, not
  a hang.

### `AllowAnonFallback` is measured, not invented

It models `preflight_auth` (`empathic/toolpath@68aacef`,
`cmd_pathbase.rs:263`): with no auth-requiring flag, absent or rejected
credentials yield `AuthMode::Anon` and **the upload proceeds**. Upstream's
own tests pin it — `preflight_falls_back_to_anon_on_401_without_auth_flags`
and `preflight_propagates_401_when_auth_required`. The constant is TRUE
exactly when `needs_auth` is false, i.e. when none of `--repo`, `--public`
or `--name` is passed.

### Two modelling choices worth knowing before editing

**`Init` starts permitted and authenticated.** Deliberate: it means every
counterexample TLC finds is a case where something that *was* allowed became
disallowed and the upload went anyway. Starting from refusal would satisfy
the invariants trivially.

**Termination stutters explicitly** (`Terminating == AllDone /\ UNCHANGED
vars`) rather than the configs setting `CHECK_DEADLOCK FALSE`. This system
genuinely terminates, and without the stutter TLC reports the terminal state
as a deadlock. Stuttering keeps deadlock checking **on**, so a genuine stall
in a non-final state would still be caught — and the runner asserts that no
deadlock is reported, so the two cannot be confused.

---

## `degradation.tla` — authority that degrades instead of refusing

The Lean arc in `Keycard/Degradation.lean` proves the pure-runner properties
for all inputs: given a revocation record, a named authority, a fallback and
an operation, what may a runner do. It cannot see that the run is not one
step.

**The credential is selected once and used for minutes.**

```yaml
GITHUB_TOKEN: ${{ secrets.BOOTSTRAP_TOKEN || secrets.GITHUB_TOKEN }}
```

Four workflows in `bounded-systems/content-catalog` read it that way
(`bootstrap.yml:50`, `aggregate.yml:48`, `enrich.yml:40`, `seed.yml:35` —
`content-catalog#10`). A 2026-08-16 credential audit revoked the PAT behind
`secrets.BOOTSTRAP_TOKEN`. The `||` did not fail; it resolved to the next
term, which is repo-scoped and read-only by org default.

Those workflows have since been repaired — `content-catalog#11` removed the
fallback, `content-catalog#13` replaced the credential with brokered
per-workflow OIDC mints — so the YAML above is a **historical citation**, not
current code. The spec models what happened; the repair owes nothing to it.

So revocation has **two distinct places to land**, and only the first is
visible to the Lean model:

- **before selection** — the `||` substitutes the weaker principal, and the
  run proceeds under an identity the policy never named;
- **mid-run** — the run is already under way, and it simply stops reaching
  new targets. Nothing errors. It exits green over a subset.

### The four configs

| config | `AllowFallback` | `GreenOnPartial` | expected |
|---|---|---|---|
| `degradation-shipped.cfg` | TRUE | TRUE | *some* invariant violated — the behaviour that shipped |
| `degradation-fallback.cfg` | TRUE | **FALSE** | `NoUndernamedEffect` violated, `NoSilentPartial` **holds** |
| `degradation-partial.cfg` | **FALSE** | TRUE | `NoSilentPartial` violated, `NoUndernamedEffect` **holds** |
| `degradation-safe.cfg` | FALSE | FALSE | clean: every invariant, plus `Termination` |

#### Why there are four

`degradation-shipped.cfg` is the incident: both faults live at once. It is
kept because it is what actually ran, but it is the *weakest* of the four
assertions — with both invariants breaking, which one TLC reports first is an
artifact of its search order, so `check.sh` asserts only that a violation
occurs there.

The middle two carry the result. **The two faults are independent, and the
pair exhibits that in both directions** — a stronger form of the same
argument `disclosure-anon.cfg` makes with one config:

- Reporting failures honestly does **not** make the effects attributable to
  the right principal. `degradation-fallback.cfg` never ships a green
  partial, and a revoked credential's work still lands under
  `secrets.GITHUB_TOKEN`.
- Removing the `||` does **not** stop a truncated run from shipping green.
  `degradation-partial.cfg` never substitutes anything, and a revocation
  landing mid-run still yields a silent partial.

This mirrors the Lean side exactly: `runnerSufficientFallback` is `Faithful`
and violates `ActsAsNamed`; `runnerBestEffort` is `ActsAsNamed` and violates
`Faithful`. Same independence, both halves.

#### How "holds" is actually checked

The two isolating configs are run under TLC's **`-continue`**, which explores
the full state space and reports *every* violated invariant instead of halting
at the first. That is what makes "the other invariant holds" a checked
statement rather than an artifact: without it, an unreported invariant might
simply break in a state the search stopped short of, and the independence
claim would be a fact about TLC's halt rather than about the model.

### The invariants

- **`NoUndernamedEffect`** — no effect ever landed under a principal the
  policy did not name. The temporal half of Lean's `ActsAsNamed`: that
  property quantifies over an outcome, this one over every instant at which
  an effect occurred.
- **`NoSilentPartial`** — success was never reported over an incomplete run.
  The temporal half of Lean's `Faithful`, and the one that would have caught
  the real consequence: the catalog is committed **and** SLSA-attested, so a
  run that silently narrowed shipped a partial artifact carrying full
  provenance. The attestation is not wrong about what it signed; it is
  signing something nobody noticed had changed.
- **`Termination`** (safe config only) — fail-closed must not mean
  fail-*stuck*. This matters more here than in the disclosure arc, because
  the fix being modelled is "refuse instead of substituting", and a fix that
  deadlocks the lane would not survive contact with anyone's CI.

### Three modelling choices worth knowing before editing

**The strictly-weaker premise is checked, not assumed.** `ASSUME
FallbackCovers ⊆ Repos ∧ FallbackCovers ≠ Repos` — a config that made the
fallback as strong as the named authority would be modelling a different
incident, and TLC refuses it outright rather than passing quietly. The Lean
counterpart is `fxGithubToken_strictly_weaker`, closed by kernel `decide`.

**`Init` starts live and unselected**, for `disclosure.tla`'s reason: every
counterexample is then a case where authority that *was* held was withdrawn
and the work proceeded anyway.

**One run, not two.** `disclosure.tla` models two sessions because its fault
is a race between a session and the owner. This fault is a race between a run
and the *credential lifecycle*, which a second run does not illuminate — the
four content-catalog workflows degraded independently and identically, and
did not interact. One run keeps the traces readable by eye.

---

## Claim boundary

These are properties of **these models**. TLC exploring every interleaving
says nothing about whether any deployed sharer re-reads consent at commit —
and the measured answer today is that it does not — nor about how any deployed
workflow handles a revoked credential. Nothing in this org consults any of it.
See the repo README.

In particular, a clean `degradation-safe.cfg` is **not** a statement that
`content-catalog`'s workflows are correct. They were repaired in YAML
(`content-catalog#11` removed the fallback, `#13` replaced the credential with
brokered per-workflow OIDC mints), with their own evidence, and that repair
owes nothing to this spec.

The warning `front-desk-scheduler/specs/lean/README.md` paid for applies
here verbatim: the 2026-07-27 bug was *not a wrong proof but a proof of the
wrong obligation*. Proving that an atomic re-check upholds
`NoUnconsentedDisclosure` says nothing about whether `path share` performs
one. It does not. Proving that refusing-instead-of-substituting upholds
`NoUndernamedEffect` says nothing about whether any workflow refuses. They
do not.
