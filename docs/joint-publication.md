# Atomic approval and endpoint publication bundles

This advances generalized-prototype future work by composing original Racket
Appendix B `$lens-gen` (source pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`,
lines 2108–2133), existing functional component closure and native FUN revision
chains. The paper does not specify multi-service transactions or runtime locking.

## One authoritative immutable bundle

`joint-publication` owns one private snapshot containing all endpoint graph heads
and all named approval objects. Native metadata remains native POO data, but edits
are staged as whole immutable replacement objects. Installed metadata is NEVER
mutated by the joint API. This avoids partial policy updates if a later endpoint,
constructor, source guard or cross-service approval fails.

`stage` validates duplicate/unknown policy and endpoint names, captures the old
snapshot and all old/proposed metadata revisions, and overlays replacements without
building a graph. `submit!` runs the existing snapshot-bound component revision
action on EVERY endpoint's exact old graph with the proposed policy lookup. An
omitted endpoint edit is an empty revision: clean receipts skip builders but still
obtain current approval. Thus policy-only changes cannot bypass an unchanged
endpoint. A final joint predicate observes the complete candidate bundle.

After all constructors, per-service approval and joint consistency succeed, the
installer locks, rechecks metadata guards and expected snapshot identity, then
replaces ONE authoritative bundle pointer. Any refusal/exception returns the actual
current bundle. A rival may have succeeded while this request prepared; the late
candidate cannot overwrite it or restore its predecessor. Refused candidates never
become retry caches. Restaging explicitly captures current source and replacement
policies again; there is no automatic rebase or retry.

Readers capture `current` ONCE, then use `head` and `approval` on that same snapshot.
Several separate `current` calls may intentionally observe different rounds; the
API cannot make unrelated reads a transaction. Historical snapshots retain their
old policies/heads. This authoritative bundle is separate from prior independent
endpoint coordinators; it does not claim atomic mutation of existing independent
coordinator handles. To use consistent joint publication, readers/writers use this
family's snapshot interface exclusively.

All registered policies, lists, source descriptors and callback dependencies remain
immutable for each snapshot/request's lifetime. Existing revision guards detect
supported edits and protect registered objects during construction. Caller-owned
replacement objects are also guarded; mutating a proposed policy after staging
invalidates that request without changing installed state. Raw/foreign writes,
hidden dependencies, arbitrary callback effects, custom reentrant mutation hooks,
crash durability and distributed transactions remain outside this protocol.

## Practical native scenes

`examples/joint-services` creates two actual compact service graphs under shared
limit=12 and independent local policies. Both endpoints must agree on settlement.
A joint batch replaces shared/local approval objects and merges both SCC workflows,
producing settlement=24 at both endpoints. Stable independent feedback receipts
retain exact identity through existing caches.

Fixed callback metadata guards are retained for every subsequent request.
Controls cover whole success and old snapshot preservation; second-service refusal
after the first candidate was constructed, retaining ALL old policies and heads;
explicit fresh retry; partial deployment rejected by final consistency; policy-only
revocation rejected even with every constructor forbidden; proposed metadata drift;
duplicate/unknown replacement targets; and a worker paused at final joint approval.
While paused, readers see the old complete bundle. A rival installs a whole new
bundle; the resumed request refuses and returns that exact winner. A newly staged
split then publishes settlement=16 at both endpoints consistently. Standard
channel/join waits retain five-second bounds inside the existing focused gate.

The native example's initial cyclic policy fixture was rejected by the native
CyclicSlot guard because slot names shadowed lexical argument names. Renaming the
arguments preserved the intended native constant policy values; the completed
controls use actual POO evaluation rather than bypassing the guard.

## Formal correspondence and limits

`Functional.JointPublication.Bundle` has dependent endpoint-head and approval
families, permitting heterogeneous contracts and metadata types. `install` reuses
the existing serialized head decision, selecting either the WHOLE candidate or
WHOLE current state. Generic proofs establish no mixed projections, refusal and
stale retention, complete successful installation and preservation of a supplied
whole-bundle validity predicate. Actual closure and complete approval establish
that validity premise separately; the model is not proof of runtime pointer swaps.

`Examples/JointComponentPublication` closes actual compact/merge/split sources with the
shared `ComponentExecution` runner. It exercises rejected metadata/head bundles,
fresh policy preparation and complete installation, stale rejection after a winner,
and restaging from the winner's current topology. Universal lens/source equations
remain separate from native pointer/thread observations. Fixture identities and
numeric policies are local proof inputs, never Scheme imports.

Scope remains accepted finite graphs, correct declared dependencies, fixed lawful
lenses, faithful builders and pure locally total callbacks. No arbitrary-effect
rollback, general convergence/leastness, interior-SCC skipping, runtime/compiler
verification, speed or GC claim. No new versioned JSON, full data or archives.

[joint-rounds.md](joint-rounds.md) adds explicit expected-bundle preparation,
multiple competing complete requests, cross-round stale batches and fresh restaging.
