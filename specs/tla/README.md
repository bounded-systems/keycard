# specs/tla — transcript disclosure, the temporal projection

The Lean arc in `Keycard/Disclosure.lean` proves the pure-policy properties
for all inputs: given a decision record, a session and an upload, what may a
policy permit. Those theorems cannot see the fault this module exists for,
because the fault is temporal.

**`path share` does not decide and upload in one step.** It runs
`preflight_auth`, then derives the graph, then uploads. The decision that
authorises the upload is read at one instant and acted on at a later one,
with the expensive derive in between. Between them the owner can withdraw
consent and a credential can expire. Bytes already sent do not come back.

So every check-then-act is split across two actions with a yield point
between, and TLC explores the interleavings — the same shape as
`front-desk-scheduler/specs/tla`, from which this borrows its discipline.

## Running it

```sh
bash specs/tla/check.sh          # fetches the pinned tla2tools, verifies its digest
TLA2TOOLS=/path/to/tla2tools.jar bash specs/tla/check.sh   # or bring your own
```

The runner **asserts** each config's outcome rather than reporting it. Two of
the three configs are supposed to fail; a runner that only printed TLC's
output would go green if a future edit quietly made the racy config pass,
which is exactly the case worth catching. A spec whose counterexamples have
stopped reproducing has stopped saying anything. This is the TLA+ half of the
anti-vacuity discipline the Lean side gets from its named counterexample
policies.

## The three configs

| config | `Atomic` | `AllowAnonFallback` | expected |
|---|---|---|---|
| `disclosure-racy.cfg` | FALSE | TRUE | `NoUnconsentedDisclosure` violated |
| `disclosure-anon.cfg` | **TRUE** | TRUE | `NoAnonUpload` violated, `NoUnconsentedDisclosure` **holds** |
| `disclosure-safe.cfg` | TRUE | FALSE | clean: every invariant, plus `Termination` |

### Why there are three and not two

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

## The invariants

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

## `AllowAnonFallback` is measured, not invented

It models `preflight_auth` (`empathic/toolpath@68aacef`,
`cmd_pathbase.rs:263`): with no auth-requiring flag, absent or rejected
credentials yield `AuthMode::Anon` and **the upload proceeds**. Upstream's
own tests pin it — `preflight_falls_back_to_anon_on_401_without_auth_flags`
and `preflight_propagates_401_when_auth_required`. The constant is TRUE
exactly when `needs_auth` is false, i.e. when none of `--repo`, `--public`
or `--name` is passed.

## Two modelling choices worth knowing before editing

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

## Claim boundary

These are properties of **this model**. TLC exploring every interleaving of
two sessions says nothing about whether any deployed sharer re-reads consent
at commit — and the measured answer today is that it does not, and that
nothing in this org consults any of it. See the repo README.

The warning `front-desk-scheduler/specs/lean/README.md` paid for applies
here verbatim: the 2026-07-27 bug was *not a wrong proof but a proof of the
wrong obligation*. Proving that an atomic re-check upholds
`NoUnconsentedDisclosure` says nothing about whether `path share` performs
one. It does not.
