# Recursive publication coordinator recovery

This advances generalized prototype/MOP future work. The Racket essay's Future
Work and Appendix B motivate representation-independent composition, type/logical
metadata and protocol extension. They do not specify this coordinator recovery
policy. The implementation composes existing FUN readers, graph closure, lens
version guards and checked evidence; it does not add a second publication engine.

`recursive-approvals.call-with-submissions` accepts `on-exit:` with the existing
coordinator outcome-thunk convention. After normal completion or a caught exception,
cleanup closes escaped queue operations and releases pending references. Only then
does the handler receive a zero-argument thunk returning all coordinator values or
raising the original exception payload, including `#f`. The default invokes that
thunk. A custom handler explicitly decides whether to propagate, recover, or return
another result. Handler errors propagate once, outside the coordinator catcher.
Invalid coordinator/handler procedures refuse before any work; unconsumed normal
return still becomes a refusal. No automatic retries or queue resurrection occur.

Recovery opens a NEW scope and stages against the actual current whole graph and
approval pair. The old scope is permanently closed; separately retained old requests
can be explicitly submitted to the new scope, but their original guards remain.
Another coordinator may have installed since exit. Reusing an exit snapshot is
therefore insufficient; fresh preparation and ordinary install-time checks are both
necessary. A post-install coordinator exception keeps the installed prefix and its
receipt. The exit record is historical evidence, not a new approval or a deep frozen
copy of mutable metadata. Already performed external effects are not rolled back.

`examples/recursive-recovery.ss` runs eight actual SCC/provider/computed revisions.
Each round a coordinator exits with two queued requests. A survivor invalidates
proposed then installed approval metadata through ABA, replays historical requests
and refuses a locally admissible but jointly over-budget candidate. Survivors win
odd rounds, recovered coordinators win even rounds. Recovery admits freshly staged
work behind retained old requests; installed approval invalidates it AGAIN before
an explicit second preparation. The 256 attempts include eight installations and
248 refusals. Fresh observation retries current refinement and exact bind-evidence
for three entry contexts, with totals 3/3/2. SCC merge/split, shared provider
migration/removal/reintroduction and computed reader/body changes reject dirty old
references while preserving the independent idle canonical reference.

The companion `Functional.RecursiveRecovery` adds nine finite pure laws: exit
preserves installed world, historical receipts and outcome; restart has no old
pending queue/history; fresh recovery sees the current world; survivors keep
revision monotonicity; rejoining prepares after survivor progress; old-round
requests remain stale; and exit after late effect refusal retains the new graph.
The executable fixture uses the same actual checked closure and evidence observers.
The model's outcome is an ordinary value/error; Scheme multiple values and exception
identity are tested separately, not proved as host-runtime semantics. A successful
formal finish represents a drained host scope; host unconsumed return is an error.

Premises remain complete dependency/version registration, identity correspondence,
immutable-in-use metadata, pure terminating formal callbacks, and serialized calls
to one owner. Forced thread/process death, asynchronous interruption inside publish,
distributed recovery, durability and concurrent CAS are outside this implementation.
Nonlocal continuation escape still performs dynamic-wind cleanup but does not
promise an exit-handler notification. This is no performance or runtime/GC proof.
Scheme builds and tests without any Lean checkout dependency.
