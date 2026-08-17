-- Root module: all five arcs, in reading order.
--
-- Arc 1 — OIDC subjects: a `sub` is locally unique and never reassigned.
import Keycard.Model
import Keycard.Recycling
import Keycard.Soundness
import Keycard.Matcher
-- Arc 2 — claim-bound signing: a guest signs issue `i` at `t` iff an
-- issuer-attested claim binds it to `i` and is live at `t`.
import Keycard.Claim
import Keycard.Signing
-- Arc 3 — identity provenance: the gate is vendor-blind; identity roots
-- must name guests injectively.
import Keycard.Identity
-- Arc 4 — transcript disclosure: what may cross the boundary to a third
-- party, under whose identity, and what may confer that.
import Keycard.Transcript
import Keycard.Disclosure
-- Arc 5 — degrading authority: a revoked keycard must shut the door, not
-- hand over a weaker one while the caller is told it worked.
import Keycard.Authority
import Keycard.Degradation

-- ENFORCEMENT PROBE (.github-private#594) — DELIBERATE TYPE ERROR.
-- This line exists to make `standard / test` report `failure`, so a merge
-- attempt against it measures whether the `ci-green-keycard` ruleset actually
-- refuses the merge, rather than inferring it from #464's probe on a different
-- repo. It must NEVER be merged; the branch is deleted once the attempt is
-- recorded. If you are reading this on `main`, the experiment leaked — revert.
example : Nat := "this is not a Nat"
