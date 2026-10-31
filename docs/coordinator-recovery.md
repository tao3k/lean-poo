# Local coordinator exit and continuing joint publication

This extends generalized-prototype future work. Original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2087–2133)
provides representation-independent composition, lenses and cooking. Local failure
isolation and concurrent publication are extensions built on those constructions.

## Explicit supervision policy

`examples/joint-coordination.call-with-coordinators` now gives each coordinator a
standard child thread group under its detached root group. Normal return and a
caught operation exception clean that coordinator's descendants before announcing
its exit. The supervisor invokes `on-exit:` exactly once for each completed
operation, whether it sees the terminal event through `next` or during final joins.
The callback receives `(name outcome)`; `outcome` is a zero-argument thunk retaining
all return values or raising the original exception object.

The default invokes `outcome`, preserving whole-scope failure propagation. An
explicit handler may inspect/catch an expected local error and allow other
coordinators to continue. A callback error still leaves the scope and cleans all
remaining groups. `next` processes terminal notifications before the next live
checkpoint. Calling it when no coordinator will checkpoint eventually times out;
terminal events are not ordinary checkpoints. No implicit retry, restaging, global
receipt revocation or rollback of an installed winner is added.

Only the supervisor consumes terminal outcomes. Completion/replies remain bounded
by the existing five-second waits; standard recursive group cleanup owns nested
threads. External processes, forced termination bypassing the operation's return/
exception path, and escaped publication capabilities are outside local isolation.
The outcome thunk may be inspected by the handler; the handler decides how to treat
it. Merely installing an `on-exit:` callback is not proof that an error was handled.

## Shared complex revision chain

`examples/joint-coordination-rounds.coordinate-revisions` extracts the existing
higher-order worker workflow for reuse. Each survivor independently captures,
constructs, closes, approves and explicitly restages; older siblings remain pending.
`t/joint-coordination-cases.check-revisions` shares all original whole-state and
SCC assertions instead of duplicating the original scenario.

`t/coordinator-recovery-test.ss` runs four real coordinator threads:

- Two survivors compete through merge / replace / restore twice. Every round
  invalidates their shared proposed policy with a B -> B+1 -> B revision trip,
  refuses both old approvals, then independently restages policy-distinct requests.
- A third coordinator fails during round two; a fourth returns two values during
  round four. Each has its own pending child installation. The exit handler checks
  that child is terminated and the authoritative bundle is still the exact
  previously installed winner before releasing the survivors' waiting workers.
- Thus exit observation is necessary to continue: without the callback the live
  checkpoint wait fails. No sleeps or chosen publication winner are used.
- Each phase has exactly one successful fresh primary, stale late siblings cannot
  publish, and two services agree on the whole winner. Settlements 24/16/12 repeat;
  deleted components/code/base disappear and the independent shared receipt is reused.
- Both exits are observed once, the original error object and both normal values
  are retained, and saved parent/child thread handles are all terminated at return.
  A separate control checks default unhandled failure aborts/joins the remaining
  sibling and preserves the exact whole owner.

The deterministic fixture cancels children waiting before installation; it does
not qualify asynchronous interruption inside a publication critical section.
A write that already linearized stays installed, independent of later parent exit.

## Formal lifecycle projection

`Functional.JointPublication.CoordinatorEvent` records an actual `attempt` or a
`stopped` coordinator. `coordinatorAttempts` projects only actual checked writes;
`installCoordinated` reuses `installSequence`. A stop is a no-write lifecycle event,
not a request to undo the preceding committed prefix.

`installCoordinated_stopped` proves that a stop anywhere leaves both the earlier
winner and all later surviving attempts unchanged. `restageAfter_coordinator_stopped`
proves explicit survivor preparation still sees the exact actual prefix snapshot.
`installCoordinated_valid` preserves validity through arbitrary finite events.
`Examples/JointCoordination` interleaves stops with guard refusal, fresh competing
publication and historical replay on actual certified SCC heads in all six phases.

The native bridge requires local cleanup to exclude the cancelled pending attempts,
plus existing owner-lock linearization, immutable installed policies, registered
guards, fresh identities, lawful lenses, correct dependencies and valid total
factories. This finite trace proof does not prove the thread runtime, scheduling
fairness, arbitrary recursive convergence or distributed/durable transactions.
Functionality is the scope of this change; no performance improvement is claimed.

Explicit replacement operations can now rejoin the live scope after cleanup/join
and outcome handling; see [coordinator-rejoining.md](coordinator-rejoining.md) for
three recoveries during the continuing six-phase workflow and old-receipt laws.
