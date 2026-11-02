# Continuing recursive submissions

`recursive-approvals.call-with-submissions` passes three scoped procedures to a
coordinator: `(enqueue! request observer)`, `(advance!)`, and `(pending?)`. They use
`:std/struct/queue` and the existing single-attempt receipt/publication path.
`advance!` returns one receipt, or `#f` when empty. Enqueue checks and copies one
procedure pair; it neither builds nor publishes a candidate. The coordinator can
prepare fresh work using `stage-with` while older requests remain in the FIFO.
Each advance checks the original request's snapshot and installed/proposed lens
revisions. Enqueue never refreshes an older request or grants renewed approval.

Normal coordinator return requires the queue to be empty and preserves multiple
return values. Exceptions release pending references and close escaped operations,
while retaining installed prefixes. Calls from an active request/observer reject
before modifying the queue. Continuation reentry after scope exit is refused.
This API requires serialized callers of the same publication owner. It supplies
no thread scheduling, concurrent CAS, distributed arrival protocol or effect rollback.
A callback failure after installation retains that installation in its receipt;
new staging or an effect-only observation must be an explicit caller decision.

`examples/recursive-submissions.ss` takes an observer factory and receipt consumer,
composing existing FUN observers. Eight rounds enqueue current/future requests
behind previous pending competitors before consuming them. Proposed-policy and
installed-policy ABA separately invalidate requests; local admission then succeeds
but joint approval refuses a fresh low-budget candidate. A fresh winner installs
before a late business refusal. Its challenger and spent winner remain pending
while the next round admits new work. Effect-only retry uses current `refine` and
exact `bind-evidence`, preserving the other entries' contexts. The 64 receipts
cover SCC merge/split, provider removal/reintroduction and shared dependency
migration, computed reader/body changes and dirty old-reference rejection; clean
independent references remain canonical. No receipt is a renewed capability.

The companion Lean `Functional.RecursiveSubmissions` proves eight finite transition
laws: exact FIFO append, admission's world/history preservation, empty identity,
head-only consumption, historical receipt prefix, step/script revision monotonicity
and permanent historical request staleness under continued arrivals. Its executable
eight-round fixture uses actual selective graph closure and checked evidence.
The model assumes complete dependency/version registration, exact identity
correspondence, immutable-in-use metadata and pure terminating callbacks. Gerbil
scope/exception controls are executable tests, not Lean proofs of the host runtime.
This advances the generalized prototype/MOP future work described in the Racket
essay's Future Work and Appendix B; the essay does not specify this publication
queue or prove distributed coordination. Scheme builds and tests independently
of any Lean checkout. No speed, allocation or GC improvement is claimed.

An optional `on-exit:` policy now receives the original outcome thunk after
cleanup; its default propagates that outcome. Explicit recovery and survivor
progress are documented in [recursive-recovery.md](recursive-recovery.md).
