# Mixed-generation concurrent installation

See [joint-restaging.md](joint-restaging.md) for a continuing scoped worker group:
later source revisions are prepared while older installation workers still wait.

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper supplies lens-based composition, not this multi-service transaction
protocol. Existing native FUN revisions, lenses, SCC closure, approved receipts,
thread rendezvous and guarded owner installation remain reused.

## Correlate each concurrent result with its receipt

`examples/joint-concurrency.install-concurrently` now accepts a pure `report:`
function of receipt, snapshot and failure. It runs in the caller while collecting
worker result thunks, outside the owner lock. The default still returns the
existing `(snapshot . failure)` pair; existing callers are unchanged. A client can
retain receipt identity or its own labels without opening private receipts or
changing installation semantics. Result order is worker-report arrival order,
not input order or a formal assertion of lock acquisition order. Report callbacks
must be pure and locally total; exceptions propagate with existing worker cleanup.

`t/joint-generations-test.ss` uses a private compact observation record with named
receipt/snapshot/failure fields. It can therefore reject an old receipt's success
DIRECTLY rather than inferring its generation from final numerical values.

## One wave contains old and new generations

Six native merge / replace / restore rounds each prepare two receipts sharing one
proposed policy and two independent current receipts. The worker list contains
ALL prior-round receipts, the four current receipts and a duplicate current valid
receipt. They become ready together and receive release tokens in the same wave.
Before release the uninstalled shared policy makes a still-admissible budget
round trip B -> B+1 -> B, invalidating the two shared-policy receipts.

The test requires exactly one success, attributed to one of the independently
approved CURRENT receipts. Every historical receipt and both current shared-policy
receipts must have a failure. Successful policy identity must match the winning
receipt's proposed policy exactly. Every returned snapshot is the pre-wave bundle
or the complete current winner, according to when its failure/current read occurs.
Five new workers plus four historical receipts per completed round produce wave
sizes 5,9,13,17,21,25. The final replay covers all 24 retained receipts.

Fresh source preparation follows each wave's actual winner. Both independent
feedback receipts retain exact identity; removed B/D or restored-away E/F lack
receipts as appropriate. E/F code/base providers are erased after restoration.
The topology/support round trip does not revive any earlier expected head.

## Entire wave refuses, then explicitly restages

Another native scenario first installs A's merge, retaining that old receipt. The
current candidate replaces A's B/D endpoints and merges B (settlements 16+24).
Two receipts share proposed budget=40. A mixed wave of the old receipt and these
two current receipts sees the proposal change 40 -> 41 -> 40 before release and
ENTIRELY refuses, preserving the exact current snapshot.

Explicit new `stage-at`/approval through the existing example helper captures the
new proposal revision and current source. The retry races alongside both failed
current receipts and the old receipt, with a duplicated fresh receipt: exactly
that fresh receipt succeeds once. A further mixed wave combines all those older
receipts with newly approved A-restore/B-replace (12+16), again requiring only the
current receipt to install. Installed policies are never mutated by these controls.

## Formal mixed-head laws and constructive controls

`Functional.JointPublication.installSequence_append` composes complete traces.
`installSequence_inert` proves a finite list of head-stale OR guard-stale receipts
preserves the exact current bundle; historical expected identities may differ.
`installSequence_mixed_winner` admits an arbitrary refused prefix, one valid
current receipt and an arbitrary refused tail. Tail refusal is evaluated against
the NEW candidate bundle. This makes the no-reuse requirement for historical
expected identities explicit rather than assuming every sibling has one old head.

`Examples/JointGenerations` certifies actual local/joint admission of candidates
whose heads retain typed sources, discovered support/SCC graphs and successful
resolver equations. At each of six source lifecycle steps it enumerates every
order of current valid alternatives, a drifted receipt and up to two far/near
historical receipts, inserting each historical receipt at every list position.
There are six orders initially and 120 per later round; only whole current
candidates may win. Final old-history replay cannot revive removed components.
The generic proofs cover arbitrary finite histories, beyond this finite fixture.

The native/formal bridge still assumes owner-lock linearization, fresh snapshot
identities, complete registered guards, immutable installed metadata, correct
explicit dependencies, lawful lenses and faithful pure locally total callbacks.
Native pointer/receipt provenance controls and formal serialized-order laws are
separate evidence. No arbitrary concurrent internal writes, global convergence,
distributed/durable atomicity, runtime implementation proof or performance claim.
