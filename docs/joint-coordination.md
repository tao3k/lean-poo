# Independent coordinators sharing a joint publication owner

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper supplies lens-based construction, not this multi-coordinator scheduler.
Existing FUN revisions, native policies, SCC closure, opaque receipts, worker
scopes and the guarded owner installation remain reused.

## Standard-library scoped supervision

`examples/joint-coordination.call-with-coordinators` runs distinct named operations
on real Gerbil threads. Each operation receives `exchange`: send a checkpoint to
the supervisor, then wait for a one-shot reply. The supervisor's `next` passes the
coordinator name, payload and reply procedure to a handler. Different coordinators
own separate `call-with-installations` scopes/counters/channels while sharing the
same authoritative publication owner.

Standard `:std/sync/channel` implements messages; `:std/sync/threads` supplies a
detached root group, per-coordinator child groups, exception-preserving joins and
recursive group cleanup.
The group owns coordinator threads and their nested installation workers. Five-
second bounds cover receives and normal joins. Original operation exceptions are
transported through event/result thunks, so ignoring an error event cannot make a
coordinator failure successful. Multiple supervisor return values are retained.
Scope closure rejects escaped supervision/reply operations and duplicate replies.
Finally uses standard recursive thread-group cleanup, rather than a custom child
thread traversal. Work already installed is not rolled back on supervisor failure.

## Two coordinators, six continuously overlapped SCC phases

`t/joint-coordination-test.ss` runs two independent coordinator operations. Each
owns its installation scope through merge / replace / restore TWICE:

1. Supervisor sends both the next phase and ONE shared proposed policy object.
   The policy is cooked before sharing; installed metadata remains immutable.
   Both coordinators independently capture current source, construct/close and
   approve their candidate, and start a waiting installation worker.
2. Only after BOTH approval calls returned does the supervisor change the
   uninstalled policy budget B -> B+1 -> B. Both budgets still admit the candidate.
   Their workers install/refuse; both return the exact pre-round bundle.
3. Both coordinators receive distinct replacement policies (budgets B and B+2),
   independently restage/approve the SAME source changes concurrently, and start
   a primary plus late sibling. Their preceding-round late workers still wait.
4. Once both fresh approvals returned, release both primaries and older siblings.
   Both coordinators independently collect their own outcomes and report them.
   Exactly ONE primary succeeds. Every older sibling fails. Results are the whole
   pre-round bundle or actual whole winner, according to the current read timing.
5. Each coordinator keeps its new late sibling pending across next-round shared
   policy refusal and explicit restaging. Only final late siblings are drained
   before their scopes finish and coordinator threads join.

Ready/reply checkpoints control source observation and release, without sleeps or
forcing a winning coordinator. Construction/admission occurs on both coordinator
threads, not on one supervisor that merely hands receipts to workers. The fixture
checks 24,16,12 settlements twice, component deletion/restoration, E/F code/base
erasure and exact reuse of independent feedback receipts.

A supervisor-failure control verifies that a coordinator group contains its pending
child installation worker, raises the original supervisor failure, checks the whole
owner is unchanged, and confirms no active thread remains in that group after
standard cleanup. It does not touch unrelated thread groups.

## Formal competing observations

`Functional.JointPublication.restageAfter_competing` proves both possible install
orders for independent valid factories observing one prefix: each order selects
its first complete candidate. `restageAfter_superseded` rejects an older captured
receipt after a different head is observed, even if joint approval and registered
revisions are still valid. `restageAfter_refused` proves explicit new preparation
after mixed head/guard refusals sees the same source bundle as before those refusals.
The dependent candidate-validity proof remains attached to the actual factory result.

`Examples/JointCoordination` certifies actual local/joint admission against typed
sources, discovered SCC/support and successful resolver equations. At six source
phases it refuses shared-revision drift, constructs both factories from the observed
head, checks both policy-distinct winners, rejects the superseded competitor and
replays earlier receipts. The successful fresh-candidate factory is shared with
the earlier restaging fixture, whose executable regression is retained.

The bridge assumes owner-lock linearization, fresh installed identities, complete
guard registration, immutable installed policies, faithful pure locally total
construction/admission, correct declared dependencies and lawful lenses. The model
covers successful valid factories; it does not promise arbitrary factories succeed.
Native threads/groups and formal lock-order laws are separate evidence. No arbitrary
internal writes, recursive convergence, distributed/durable atomicity, runtime
implementation proof, scheduler fairness, multi-core throughput or speed claim.

Local coordinator failure isolation and continuing survivors now compose through
an explicit `on-exit:` handler; see [coordinator-recovery.md](coordinator-recovery.md)
for the outcome protocol, six-round four-coordinator scenario and lifecycle laws.
