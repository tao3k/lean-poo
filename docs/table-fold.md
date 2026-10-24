# Complete incremental fold admission

This is a finite implementation unit of the collection proposal's future work.
It closes whole-root admission for owner-bound aggregate states and their explicit
isomorphism transfers, not automatic algebra or symmetry discovery.

## The missing boundary

Compatible delta descriptors share Key/Value Types; they need not share complete
root refinements. Previously a delta prepared through an unrestricted backend
could leave a refined fold's successor invalid while its aggregate remained
readable. A warm isomorphism transfer could likewise replay valid child bindings
into a target that refused the complete resulting root. Both paths reproduced
`root-admitted? #f` with a returned aggregate of 20 from the same two-entry base.
Lawful key/value bijections do not establish arbitrary whole-target constraints.

## One final-state protocol

`table-fold` now reuses `require-table` on the complete installed source root,
before contribution callbacks. The fold bridge reuses the same boundary on the
complete translated target, before adopting the aggregate and replacing its
private pairing. Complete recognition retains admitted leaves; it does not run
recursive normalization again. No extra carrier, cache registry, namespace or
second implementation of delta installation is introduced.

Only the final root is recognized. A composed removal/insertion may cross an
invalid intermediate root and still publish a valid final root. Existing ordered
old-value conflicts and collision checks are retained. Source recognition refusal
suppresses contribution callbacks. Target recognition refusal may follow source
contribution evaluation and translation; their external effects cannot be rolled
back. Neither refusal publishes a fold state, replaces the accepted pair nor
reaches the FUN/IO consumer. Recognizer/backend exceptions preserve their cause.
Supported metadata mutation is guarded throughout. Repair requires a fresh valid
request, not relaxed recognition or silent refresh of expired declarations.

Cold target conversion already recognized its result. Warm replay now obeys the
same constraint. Pair hits still reuse the existing admitted state; inverse
conversion and independently fresh same-root rebinding retain their existing
origin/ownership checks. Inverse delta installation separately admits the recovered
root. A failed attempt does not discard the previous accepted pair or key registry.

## Complete service example and regression

`make-capacity-ledger` accepts ordinary Gerbil `source:` / `target:` descriptor
refinement functions, reusing its existing UInt XOR, Tuple/Pair conversion,
checked Function admission and fold bridge. `t/table-fold-test.ss` combines a
source cardinality constraint with an independent target capacity limit. Refused
publication suppresses IO, repaired publication preserves the exact admitted
Function, and inverse recovery restores the original sum and callback identity.
Other controls cover compatible unrefined deltas, private invalid intermediate
roots, cold/warm target refusal, exact recognizer failures, protected mutation,
previous-pair retention and retry. Existing sparse-projection tests retain their
refold/conversion prohibitions and explicitly observe complete backend admission.

## Laws and cost boundary

Lean `TableFold` reuses `applyChanges`, `foldChanges`, `foldView` and inverse laws.
It proves installation/refinement failure ordering, successful-root validity under
a faithful recognizer, full-fold agreement, checked inverse recovery, independent
target refusal and exact opaque aggregate reuse. Concrete decidable ledger deltas
use finite callback identities with an explicit interpretation; arbitrary closure
equality is not inferred. Scheme separately tests actual checked procedure identity.

`reuseFoldWork` now charges supplied source and target admission visits. Sparse
contributions remain bounded by twice the edit count and target reprojection is
absent. Complete root recognition can scan the snapshot and execute user
predicates; it is not a constant-cost or zero-scan operation. Metadata, registry,
backend preparation, allocation and GC require separate costs. Persistent carrier
laws, finite inventory coverage, faithful recognition and stable callbacks remain
premises; compiler/runtime correctness and arbitrary callback termination are not
proved. These semantic/cost laws establish no end-to-end speedup.
