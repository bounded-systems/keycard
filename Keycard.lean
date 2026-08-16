-- Root module: all four arcs, in reading order.
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
