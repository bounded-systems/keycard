import Keycard.Model
/-!
# Session-transcript disclosure: the model

The structures behind one question:

> When may a session transcript cross the boundary to a third party, and
> under whose identity?

A transcript is not a diff. It carries the conversation, the tool calls and
the dead ends — so it can carry secrets, tokens, internal hostnames, and the
contents of private repositories. That makes an upload a **privileged
effect**, and this file models what may confer it.

This is the same shape as `Claim.lean` one boundary over. There, the
question was what may confer *signing*; the answer was an issuer-attested,
time-indexed claim, and the theorem that mattered was that ambient state
confers nothing (#521). Here the question is what may confer *disclosure*,
and the same discipline applies: the decision belongs to a record the owner
writes, not to a variable the session can set.

## What is irreversible here, and why that changes the shape

A lease can be reaped and a claim released. **An upload cannot be un-sent.**
`Upload.revocable` is therefore not a nicety — it is the difference between
a mistake that can be corrected and one that cannot. Pathbase lets only the
*owner* replace or re-share a graph, so an upload made anonymously has no
account from which to delete it. That is modeled directly, because it is the
property that makes the anonymous endpoint categorically worse than no
sharing rather than merely less good.

## Why `Bool`, and why `none` is a state

Every predicate lands in `Bool`, for `Claim.lean`'s reason: the checker and
the theorems should be one artifact.

`Policybook` is `Option Decision`, and `none` is not a placeholder — it is
**the org's state today**. No owner decision about transcript disclosure
exists. A policy that treats the absence of a decision as permission is
`policyFailOpen` below, and it is the bug this whole file exists to name.

Everything here is a property of *this model*. That any deployed sharer
refuses correctly is a separate, labeled claim — see the README.
-/

namespace Keycard.Disclosure

/-! ## Repositories and sessions -/

/-- Repository visibility. `sourceAvailable` is its own case rather than a
    flavour of public: `prx` is PolyForm Noncommercial, readable by anyone,
    which for disclosure purposes is what matters — the licence restricts
    use, not reading. -/
inductive Vis where
  | privateRepo
  | sourceAvailable
  | publicRepo
deriving DecidableEq, Repr

/-- A repository a session read. -/
structure Repo where
  id  : Nat
  vis : Vis
deriving DecidableEq, Repr

/-- A session, modeled by the only thing that matters for disclosure: what
    it read. A transcript's sensitivity is inherited from its inputs — this
    is the model's central simplification, and it is deliberately
    conservative, since a session that read a private repo is assumed to
    have the private content in its transcript. -/
structure Session where
  reads : List Repo
deriving Repr

/-- Did this session read anything private? -/
def Session.touchedPrivate (s : Session) : Bool :=
  s.reads.any fun r => decide (r.vis = Vis.privateRepo)

/-- A session that read only public repositories. -/
def Session.publicOnly : Session := { reads := [{ id := 0, vis := .publicRepo }] }

/-- A session that read this repository — `.github-private`. The state of
    every session that has ever run this org's bootstrap. -/
def Session.readPrivate : Session :=
  { reads := [{ id := 0, vis := .publicRepo }, { id := 1, vis := .privateRepo }] }

/-! ## Uploads -/

/-- The identity an upload lands under.

    `anon` is not "no account" as a neutral default — it is the state the
    vendor CLI falls back to when credentials are absent or rejected, and it
    is the one that cannot be undone. -/
inductive Owner where
  | anon
  | account (id : Nat)
deriving DecidableEq, Repr

/-- Server-side listing. `unlisted` means addressable by UUID and not
    listed — which is the vendor default, and which is **not** privacy. -/
inductive Listing where
  | unlisted
  | listed
deriving DecidableEq, Repr

/-- Who can actually read the transcript once it is up. -/
inductive Audience where
  | urlHolders
  | everyone
deriving DecidableEq, Repr

/-- A transcript upload.

    `urlPublished` is the field that makes this model say something the
    vendor's own settings cannot: the listing is a server-side property, but
    whether the URL is world-readable is decided **here**, by putting it on a
    pull request. The two compose, and the composition is theorem
    `unlisted_published_is_public`. -/
structure Upload where
  owner        : Owner
  listing      : Listing
  redacted     : Bool
  /-- The URL was posted somewhere world-readable — a public PR. -/
  urlPublished : Bool
deriving DecidableEq, Repr

/-- **Revocability.** Only the owner may replace or delete a graph, so an
    anonymous upload can never be withdrawn by anyone. -/
def Upload.revocable (u : Upload) : Bool :=
  match u.owner with
  | .anon      => false
  | .account _ => true

/-- Who ends up able to read it. An unlisted upload protects nothing once
    its URL is published; a listed one protects nothing regardless. -/
def Upload.audience (u : Upload) : Audience :=
  match u.listing with
  | .listed   => .everyone
  | .unlisted => if u.urlPublished then .everyone else .urlHolders

/-! ### Named uploads, drawn from the real situation -/

/-- What today's `path share` produces from an unauthenticated session:
    the anonymous endpoint, unlisted, unredacted, URL destined for a PR. -/
def uploadAnon : Upload :=
  { owner := .anon, listing := .unlisted, redacted := false, urlPublished := true }

/-- An authenticated upload under the org identity, unlisted, URL on a PR. -/
def uploadAuthed : Upload :=
  { owner := .account 1, listing := .unlisted, redacted := false, urlPublished := true }

/-- The same, redacted. -/
def uploadRedacted : Upload := { uploadAuthed with redacted := true }

/-! ## The owner's decision

The analogue of `Claim.lean`'s `Ledger`: a record only the owner writes.
`SessionStep` below has no constructor that touches it. -/

/-- An owner's disclosure decision.

    `owner` is the account shares land under. It is part of the *decision*
    rather than a free choice at upload time because "which identity does
    this appear under" is exactly one of the questions being decided — the
    configured identity today is a personal dev account, a recorded
    deviation from the dedicated-org-identity recommendation. -/
structure Decision where
  /-- May a session that read a private repository share at all? -/
  allowPrivate     : Bool
  /-- Must the transcript be redacted before it leaves? -/
  requireRedaction : Bool
  /-- The account uploads must land under. -/
  owner            : Nat
deriving DecidableEq, Repr

/-- The owner's decision record. **`none` is the state today** — no decision
    about transcript disclosure has been made. -/
abbrev Policybook := Option Decision

/-- A decision permitting only public-repo sessions, unredacted, under the
    org account. The narrowest decision that permits anything at all. -/
def Decision.publicOnly : Decision :=
  { allowPrivate := false, requireRedaction := false, owner := 1 }

/-- A decision permitting private-repo sessions, redaction required. -/
def Decision.privateRedacted : Decision :=
  { allowPrivate := true, requireRedaction := true, owner := 1 }

/-! ## Guest-side authority

What a session can do on its own. Read the constructors as exhaustive: a
session may set environment variables and may observe the network. There is
no constructor that writes a `Decision`. That absence is the disclosure
analogue of `holdsClaim_guest_invariant`, and
`decision_session_invariant` proves it. -/

/-- Session-mutable ambient state.

    `shareEnv` is `BOUNDED_PATHBASE_SHARE` — an ordinary environment
    variable, writable by anything running in the session, exactly as
    `commit.gpgsign` was in #521.

    `serviceReachable` is ambient in a different way: the session does not
    choose it, but it also cannot authenticate it. Both belong here because
    the question a policy must answer is whether *either* may move the
    disclosure decision, and the answer for both is no. -/
structure Env where
  shareEnv         : Bool
  serviceReachable : Bool
deriving DecidableEq, Repr

/-- The ambient state of a session that has done nothing unusual: the
    variable unset, the vendor host not on the egress allowlist. -/
def Env.stock : Env := { shareEnv := false, serviceReachable := false }

/-- The variable set — one `export` away from `Env.stock`. -/
def Env.shareOn : Env := { shareEnv := true, serviceReachable := true }

/-- Everything a session can do without the owner. Note what is absent. -/
inductive SessionStep where
  /-- `export BOUNDED_PATHBASE_SHARE=on`. -/
  | setShareEnv (b : Bool)
  /-- Observe (or lose) egress to the vendor. -/
  | setReachable (b : Bool)
deriving Repr

def SessionStep.apply (s : SessionStep) (e : Env) : Env :=
  match s with
  | .setShareEnv b  => { e with shareEnv := b }
  | .setReachable b => { e with serviceReachable := b }

/-- A world: the owner's decision, plus the session's ambient state. -/
structure Situation where
  book : Policybook
  env  : Env

def Situation.step (w : Situation) (s : SessionStep) : Situation :=
  { w with env := s.apply w.env }

/-- Run an arbitrary sequence of session actions. -/
def Situation.run (w : Situation) : List SessionStep → Situation
  | []      => w
  | s :: ss => (w.step s).run ss

end Keycard.Disclosure
