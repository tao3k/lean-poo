# Competing staged component requests

This is finite generalized-prototype future work. Original Racket Appendix B
`$lens-gen` (source pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines
2108–2133) supplies the lens/wrapper construction, not a concurrent transaction
algorithm. This increment composes the existing source revision, FUN Reader,
whole-SCC closure, registered lens guards and joint service approval.

## Authoritative publication boundary

The previous snapshot-bound action checked the snapshot supplied by its caller.
`component-publication` adds a private coordinator holding the actual current
approved graph and a standard native mutex. `stage` captures that graph and the
existing component revision action without constructing candidates. `submit!`
reads the authoritative head, rejects a stale request before work, executes the
existing construction/approval chain outside the lock, then checks expected/head
identity again under the short installation lock. Only that boundary installs a
candidate. Native `with-lock` is reused rather than introducing synchronization
primitives. The locked installer runs no user callback. Explicit registered guards
are rechecked inside the final installation lock. Coordinated concurrent approval
writes use `revise-approval!` under that SAME lock; see [approval-revision.md](approval-revision.md).

A sibling may advance the head while a request builds or approves. The old
candidate then refuses installation even if its own construction and approval
succeeded. Refusal and exceptions return the CURRENT coordinator head plus a
failure; they must not restore the request's old predecessor over a successful
rival. A request belongs to exactly one coordinator. Even a successful no-op
publication makes old siblings stale, since identity and approval lifecycle matter.

This is optimistic head arbitration, not automatic merging/rebasing. A failed
request can be retried only while its expected publication remains current and
its metadata guards remain valid. Policy revisions require fresh preparation;
a rival publication requires a new request against current topology. Refused
candidates never become a publication or retry cache. No arbitrary callback
side-effect rollback is promised.

## Practical examples and controls

`examples/component-requests.ss` composes the existing multi-round service recipes,
lens family, whole-group builder and both current service policies. Its small
higher-order staging adapter adds an optional admission continuation for controlled
interleaving. Production constructors/approval predicates remain pure and locally
total; nested submission is used explicitly as test scheduling, not as a new
implicit component dependency.

Native controls include:

- Two requests staged from the same compact source; first acceptance makes its
  sibling stale before any builder or approval is called.
- A rival publishes spare=5/settlement=30 while an older settlement=24 candidate
  is in approval; the older candidate cannot overwrite the rival.
- A real worker thread paused at approval using standard bounded channels. Its
  sibling publishes before it resumes, so the late installation refuses. Waiting
  and joining retain fixed five-second bounds inside the existing 90-second test.
- An approval exception after a rival succeeds returns the rival as current.
- One service refuses joint approval, retaining exact old head; policy revision
  invalidates old guards and a freshly staged request rebuilds and can succeed.
- A rival wins after refusal; retry must use its current merged topology, then
  split and restore in later rounds. Old requests still refuse after values return.
- Wrong-coordinator refusal and no-op sibling invalidation.

The thread control schedules a bounded supported interleaving; it is not exhaustive
SMP verification. Metadata shared between candidate computations stays immutable;
existing parameterized object guards protect supported writes in the operation,
not arbitrary foreign-thread mutation or hidden callback state. The coordinator
lock protects the authoritative head. It does not make all POO objects thread-safe.

## Lean correspondence and proof scope

`Functional.ComponentPublication.install` models the serialized installation
choice over abstract decidable snapshot identities. Generic proofs establish:
accepted installation selects exactly the candidate and implies current=expected
and approval=true; stale candidates preserve current; approval refusal preserves
current; a first fresh acceptance defeats its predecessor's sibling; refusal permits
retry if the head remains unchanged and fresh current approval is supplied.
Fresh native object identity, truthful approval and faithful locking remain
implementation premises; the Lean model is not a proof of the runtime mutex.

`Examples/ComponentRounds.requestsCheck` constructs both actual typed source
revisions, discovers groups and closes their real equations with the shared
`ComponentExecution` runner. It checks settlement=24 and 30 candidates, rejected
late install, cross-service refusal, current-policy retry and a freshly staged
split of the winner yielding settlement=20. Local snapshot numbers are fixture
identities only; Scheme does not read them or depend on a Lean checkout.

Finite declared graph/lens families, correct declared reads, accepted certificates,
immutable/extensional metadata, pure locally total callbacks and faithful builders
remain premises. General convergence/leastness, hidden dependencies, interior-SCC
skipping and unrestricted knots remain open. Formal head-selection laws, native
pointer/thread controls, full local gates and exact-head CI are separate evidence.
No compiler/runtime correctness or performance improvement is claimed. No new
versioned JSON, full benchmark corpus or archives are committed.

[approval-revision.md](approval-revision.md) extends this workflow with several
paused requests, policy change-back invalidation and explicit fresh restaging.
