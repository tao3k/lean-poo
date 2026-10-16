# Atomic asymmetric topology and shared budget revisions

This advances the generalized-prototype future work from original Racket Appendix B
`$lens-gen` (source pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines
2108–2133). It reuses existing component graph revisions, supported SCC discovery,
lenses, controlled whole-group closure, FUN revision actions and joint snapshots.
The paper does not specify these multi-service atomic lifecycle transactions.

## Different endpoint graphs, one current approval

`examples/joint-topology` uses the same two native service families, but replaces
the equal-settlement requirement with a practical shared TOTAL budget. Each service
still independently checks current support, complete endpoint pairs, actual component
equations, monitor, settlement and shared/local ceilings. Final joint admission
bounds the sum of the two complete settlements. Different component support and
SCC membership therefore coexist without weakening either local contract.

`Change.` is ordinary POO metadata with existing phase and input edits. The higher-
order `stage-current` reads one current bundle, derives the new shared native policy
with ceiling/budget, and maps each endpoint's own lifecycle descriptor to existing
contributions. It delegates to `stage-with`; no second graph representation,
manual owner table, partial publication or implicit rebase is introduced. Omitted
endpoints reuse clean receipts but must still reapprove under the proposed policy.

## Complex native rounds

The seven-round workflow has these endpoint settlements and joint budgets:

| Round | Endpoint A change | Endpoint B change | A / B | Budget |
| --- | --- | --- | --- | --- |
| 1 | Add E/F bridges, merge, spare=2 | unchanged compact | 12 / 12 | 24 |
| 2 | Delete B/D, split | Add E/F, merge | 8 / 24 | 32 |
| 3 | Restore B/D, remove E/F | Delete B/D, split | 12 / 16 | 28 |
| 4 | Add E/F, merge, spare=5 | Restore B/D, remove E/F, quota=2 | 30 / 8 | 38 |
| 5 | Delete B/D, split | Add E/F, merge | 20 / 24 | 44 |
| 6 | Restore B/D, remove E/F | Delete B/D, split | 12 / 16 | 28 |
| 7 | unchanged compact | Restore B/D, remove E/F, quota=3 | 12 / 12 | 24 |

Each successful whole bundle invalidates its staged sibling. An original merge
request remains stale after equal settlement/approval values return. Independent
feedback receipts at BOTH endpoints retain exact identity. Removed E/F have no
current receipt and both code/base namespaces are erased. The initially untouched
endpoint's actual receipts are reused even while the other endpoint changes SCCs.

Separate controls reject total budget=35 for a 24+12 candidate and then explicitly
restage budget=36; and reject budget=27 for simultaneous restore/split 12+16 before
restaging budget=28. Whole old graphs and shared policy survive failure. A no-op
bundle retains unchanged policy identity. An initial negative fixture attempted
restoration before B/D had been deleted and was correctly rejected as a stale
membership edit; the final budget control first establishes the valid pre-state,
so its refusal is specifically the cross-service budget condition.

## Dependent Lean replacements and actual certified heads

`Functional.JointPublication.Revision` (module `Functional.JointRevision`) stages unique typed endpoint and policy lists
into one immutable candidate. It reuses `GeneralizedGraph.selectEdit` and proves
exact dependent head/approval writes and unchanged omitted fields. Existing whole-
bundle installation, stale-batch and trace-validity laws compose with it. The bundle
and revision are universe-polymorphic: a head can retain the actual higher-universe
typed source, discovered supported graph and successful resolver-equation receipt,
rather than only a first-order numerical projection.

`Examples/JointTopology` stores precisely those certified heads. It closes actual
compact, merged, replacement and restored recipes with `ComponentExecution`, stages
A merged/B compact, then A split/B merged, then A restored/B split. It checks
independent active supports, total-budget refusal with unchanged old policy,
fresh candidate restaging, exact endpoint sums, removed memberships and cross-round
stale rejection. This uses the default spare=4 variant (24+12,16+24,12+16); native
controls include that variant as well as the seven-round input-migration variant.

Finite declared key/lens families, correct dependencies, accepted graph certificates,
immutable descriptors/policies and faithful pure locally total callbacks/builders
remain premises. Typed write/frame laws and actual resolver equations are separate
from native object identity/cache work controls. No arbitrary rollback, hidden
callback dependency inference, general convergence/leastness, interior-SCC skipping,
runtime/compiler correctness, speed or GC claim. No new versioned JSON, full
benchmark data or archives are committed.
