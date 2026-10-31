# Failed coordinators rejoining a continuing publication scope

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2087–2133).
Lens-based composition, representation cooking, existing FUN revisions, SCC
closure, guarded receipts and the one authoritative owner remain reused.
The restart supervisor is an extension; it is not an algorithm supplied by Racket.

## Explicit new operations

`examples/joint-coordination.call-with-coordinators` accepts `restart:`. After a
completed operation's children have been cleaned and its parent thread joined,
the supervisor invokes `on-exit:` with the original outcome. If that handler returns,
live `next` processing may call `restart(name)`. Return a fresh operation procedure
to join under the same name, or `#f` to leave it stopped. A replacement has a NEW
child group, inbox, reply lifecycle, worker scope and receive counters. Old reply
closures remain closed. Completion callbacks and restart decisions are serialized
on the supervisor, while other coordinators keep their existing scopes.

Default restart returns `#f`; default `on-exit:` propagates the original exception
before any restart policy runs. A malformed replacement or callback exception
leaves the scope and triggers standard root-group cleanup. There is no automatic
restaging/reapproval, receipt conversion, rollback or global revocation. The caller
must explicitly choose recovery and construct from the current authoritative head.

Normal supervisor return closes live checkpoint consumption. Final joins observe
all remaining outcomes, including every launched incarnation, but never run a
restart policy. Thus final cleanup cannot secretly launch another operation after
the supervisor has returned. Receives and joins retain their five-second bounds;
whole harness bounds are unchanged. This is scoped finite recovery, not a promise
of progress for a policy that indefinitely replaces immediately failing operations.

## Three recoveries during six SCC phases

`t/coordinator-rejoining-test.ss` reuses `coordinate-revisions` and the shared
`check-revisions` assertions. Coordinator names a/b remain alive for all six phases.
Coordinator c fails three times and rejoins three times in the SAME supervisor:

1. Initial c holds an approved receipt and pending installation worker. During
   merge, its shared proposal undergoes a B -> B+1 -> B revision trip and it fails.
   Cleanup/join is observed before releasing a/b; a new c operation is launched.
2. At replace, c explicitly replays archived receipts against the actual winner,
   verifies every refusal preserves that whole snapshot, and enters the existing
   service revision chain. Three independently prepared fresh primaries compete.
3. At restore, c is failed after fresh approval but before release; its current
   primary and older sibling are cleaned. a/b still compete and publish. c rejoins
   at the next merge, then fails/rejoins again across replace/restore.

Every round invalidates the common proposed approval, refuses the earlier
requests, explicitly restages and admits fresh policy-distinct candidates. Active
participants vary by phase: c's failed incarnation has no published checkpoint;
its next incarnation enters only after the previous round's winner is installed.
Exactly one fresh primary succeeds, old late workers cannot overwrite a winner,
both services agree, settlements 24/16/12 repeat, deletions erase component/code/base
and the independent shared dependency receipt is reused.

The shared assertion helper collects exactly the declared active names. Its
higher-order release operation can address a subset of ready coordinators; no
sleeps, forced race winner or duplicated SCC assertions are needed. Saved parent
and child handles must be terminated before each local recovery callback and at
scope return. Three failures plus final normal completion produce four c exits.

Separate controls reject an old reply after a replacement starts, ensure unhandled
original failure prevents a configured restart, and preserve multiple supervisor
and operation return values while final joins suppress restart callbacks.

## Formal meaning and bounds

`Functional.JointPublication.CoordinatorEvent.rejoined` records a lifecycle event
without a write. `installCoordinated_rejoined` preserves the whole installed trace
around that event. `restageAfter_rejoined_expected` binds explicit fresh construction
to the actual prefix head, including all publications made during absence.
`rejoined_receipt_refused` rejects an old receipt when EITHER its captured head is
obsolete OR its registered guard revision changed. `Examples/JointCoordination`
executes these combinations on six certified SCC phases, including head-only and
same-head guard-drift refusals after rejoining.

Restart alone does not revoke a still-current head/guard receipt. Refusal depends
on the existing snapshot and guard checks, not on a coordinator name or a new
unrelated epoch. Rejoining alone never makes an obsolete receipt current again.
The proof assumes valid total factories, correct dependencies/lenses, fresh owner
identities, immutable installed policy, complete guards, lock linearization and
cleanup excluding cancelled pending attempts. Waiting children are the native
cancellation control; interruption inside a critical section is not qualified.
No runtime proof, fairness, arbitrary convergence, distributed/durable atomicity
or performance improvement is claimed.

Named recovery callbacks now compose multiple interleaved failed coordinators; see
[coordinator-interleaving.md](coordinator-interleaving.md) for five recoveries, delayed
rejoining, mixed historical refusals and formal lifecycle-wave preservation.
