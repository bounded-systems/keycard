# Does OIDC apply here?

The standing question, asked wherever a credential crosses a boundary — a
workflow authenticating to a registry, a room presenting itself to a
verifier, a scheduled job touching an API. Four checks; each "yes"
strengthens the case for federation over a stored secret.

1. **Is there a workload identity?** A process whose provenance — repo,
   workflow, ref, room, floor — is known at issuance time. If nothing about
   the workload is knowable when the credential is minted, there is nothing
   for a token to assert.

2. **Is there a long-lived secret standing in for that identity?** Every
   stored token OIDC could replace is standing attack surface: it works for
   whoever holds it, from wherever they hold it, until someone remembers to
   rotate it.

3. **Can the relying party verify claims?** Either directly (it federates
   with the issuer and checks signatures itself) or via a broker that does.
   A relying party that can only compare a bearer string cannot consume a
   keycard.

4. **Is the subject immutable?** If the `sub` is built from recyclable
   names, the trust is to a *label*, not an identity — the recycling
   counterexample (`Keycard/Recycling.lean`) applies. Pin `NAME@ID`, or
   match immutable side-claims (`repository_id`), or the answer to the
   whole rubric is "not yet."

## From prose to ratchet

The rubric is prose today; the mechanical form is an org audit that
inventories long-lived secrets (Actions and Dependabot secret names are
listable per repo and org) and flags each one OIDC could replace. A new
stored secret makes the audit ask the question; suppressions are explicit
and reviewed. The audit's *spec* belongs here; its plumbing belongs with
the org's other plumbing. (Same split as the rest of the org.)
