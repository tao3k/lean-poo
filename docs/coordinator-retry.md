# Failure during recovery preparation and interleaved retry

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2087–2133).
The underlying lenses, cooking, FUN revisions, SCC closure and guarded whole-owner
publication remain reused. Recovery preparation and supervision are extensions,
not concurrent algorithms supplied by the paper.

## Prepare before continuing

`examples/coordinator-rejoining.rejoin-after` composes a preparation operation and
a continuation inside a replacement coordinator's own group. Preparation receives
its exchange function; success passes exchange followed by ALL preparation return
values to the continuation via standard `call-with-values`/`apply`. A preparation
exception is neither wrapped nor retried locally. It exits through the existing
cleanup/join/outcome/recovery chain, where the named policy decides what to do.
No continuation runs for that failed preparation.

Resource ownership stays with the preparing operation. The example uses a standard
nested thread group and `finally` cleanup. A successful preparation cleans/joins its
resource child before entering the service chain; a failed one cleans resources
and its parent is joined before the next named recovery decision. This combinator
adds no publication authority, implicit fallback, rollback or automatic reapproval.

## Four failures before rejoining, alongside three active failures

`t/coordinator-retry-test.ss` reuses the existing continuing service operation and
shared whole-state assertions across six merge / replace / restore phases:

| Round | SCC phase | Service participants | Recovery action | Active failure |
| --- | --- | --- | --- | --- |
| 1 | merge | a/b/c/d | replacements begin preparing | c and d |
| 2 | replace | a/b | c and d fail preparing and retry | none |
| 3 | restore | a/b/d | c fails preparing again; d succeeds | none |
| 4 | merge | a/b/c/d | c succeeds | d |
| 5 | replace | a/b/c | d fails preparing and retries | none |
| 6 | restore | a/b/c/d | d succeeds | none |

Both orders of the two-name preparation failures are tested. a/b keep the same
installation scopes throughout. Preparing replacements can remain paused while
other coordinators complete a source phase. Success captures the current snapshot
AFTER resume, explicitly refuses archived old receipts, then enters the SAME
service revision chain. Preparation failures mint no requests or approvals.

A standard FIFO channel retains service checkpoints intercepted while supervision
drives a preparation failure/retry. `channel-try-get` explicitly performs the
nonblocking read; retained checkpoints are neither acknowledged nor lost. The
buffer must be empty when the supervised workflow returns. Five-second waits and
original whole-harness bounds remain unchanged; no sleeps choose publication order.

Each phase invalidates shared proposed metadata by a B -> B+1 -> B revision trip,
refuses old approvals, freshly prepares candidates and obtains exactly one
successful primary. Checks retain whole snapshots, historical sibling rejection,
24/16/12 settlements twice, component/code/base erasure and independent shared
receipt reuse. Saved parent/child handles must terminate before each failed
instance's recovery callback and at final return. c has one active failure and
two preparation failures; d has two active failures and two preparation failures.
Only one c preparation and two d preparations reach the continuation. The prepared
snapshot/count/resource tuple and cleanup-before-continuation are checked.

A separate unknown-error control preserves the original preparation exception,
cleans a live peer and proves the continuation never ran. Initial focus timed out
on the empty-buffer receive; a shorter diagnostic confirmed the location. The
final fixture uses the standard nonblocking API and the original acceptance bound.
These earlier diagnostic logs are local only, not committed benchmark material.

## Fallible preparation model

`Functional.JointPublication.prepareRejoining` accepts a pure factory returning
`Except Error {candidate // Valid candidate}`. `prepareRejoining_failed` preserves
the exact error with no receipt; `prepareRejoining_success` preserves the valid
candidate/proof and captures the actual explicitly supplied current head.
`rejoiningAttempts` projects successfully prepared installation requests while the
original `Except` results retain their errors. `installRejoining` reuses all existing
owner checks. `installRejoining_failed` erases a failed preparation anywhere without
rolling back a committed prefix or cancelling successful later peers.
`installRejoining_valid` preserves validity across arbitrary finite mixtures.

`Examples/JointCoordination` combines repeated errors from both names, old receipts
from prior rounds/current guard drift, successful new preparation, both fresh
winner orders and post-publication errors on six actual certified SCC phases.

The bridge assumes read-only preparation before success, valid total successful
factories, correct dependency/lens laws, complete guards, immutable installed
policies, fresh identities, lock linearization and cleanup excluding cancelled
pending attempts. Arbitrary preparation side effects are not rolled back. Old
receipt refusal still requires stale head or guard revision. No critical-section
interruption, thread-runtime proof, fairness, eventual recovery, arbitrary
convergence, durable/distributed atomicity or performance improvement is claimed.
