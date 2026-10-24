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

## Composed target construction and installation

A second concrete omission concerned whole target operations. A valid two-owner
unique-index swap succeeded through the index's own `.apply-delta` but failed
through the fold bridge, which issued `.acons` one row at a time. An order view
also inherited the point-write fallback. Cold conversion likewise inserted rows
individually, so a valid complete family could fail on a forbidden singleton.
These are protocol composition defects, not automatic optimization research.

The common table protocol now exposes `.key-table value-type`: a persistent key
space with that payload Type and the same lookup equality. Parametric backends
explicitly declare payload rebinding and structural child recognition, dropping business-root
refinements. Closed indexed families delegate to their primary key space. Order
views delegate lookup equality rather than inferring it from traversal order.
Representation Wrappers reuse `table-wrapper` with the original key isomorphism,
an identity carrier and an identity payload map. They do not apply the original
business-row carrier conversion to owner IDs. Endpoint Key/Value identities are
checked, and existing guards protect capability getters and declared metadata.
An absent capability refuses explicitly. A user backend must supply this law for
its actual equality; no hash equality,
comparator or arbitrary constructor polymorphism is inferred.

Cold conversion prepares bindings in source visitation order with Gerbil's
`with-list-builder`, then calls the target's bulk constructor (spelled
`.<-list` in code) once. Index construction recognizes the complete primary and
builds each cache family once. Ordered and representation views preserve the
source constructor. Individual conversion failures occur before that constructor
is invoked; its backend/recognizer exceptions retain their exact cause.

Warm transfer prepares a private key-space overlay containing its last translated
edit at each touched key. The next expectation comes from that record or the
issued target snapshot. A known removal, an untouched key and a stored false are
separate states. Only keys and present replacements are converted; old target
rows are retained without conversion. All repeated edits and origin dependencies
remain in one delta. The target's existing `.apply-delta` runs once, and order
views preserve that delegation. Complete final-root admission still precedes
aggregate adoption and cache publication. Removed key owners remain reserved
until all requested mappings pass collision checks and installation succeeds.

Failure preserves the previous pair and suppresses the FUN/IO consumer. Target
backend effects and source contribution effects are not rolled back; no mutable
owner is consumed by these persistent fold states. Explicit retry starts with a
fresh valid request, and inverse recovery uses the same complete installer.
The constructor-owned origin discipline also applies to empty batches.

`make-service-ledger` reuses the existing two-identifier/shared-team service
factory, counted fold and caller-supplied presentation. The integrated example
composes indexes, explicit order and boxed key representation; it rejects a real
identifier conflict, publishes both identifier swaps and team migration together,
then undoes them while preserving the admitted Function objects. Regression also
prohibits target point writes, checks complete cold construction, repeated
remove/reinsert with false values, exact conversion failures, stale declarations,
and mistyped or interfering key-space getters.

The existing table module includes its fold implementation from `table/fold.scm`;
no public namespace or duplicate collection engine is introduced. Lean's
`keySpaceView_replace`, `overlayView_replace`, `traceBindings_apply`,
`traceBindings_transport` and `traceBindings_index` connect the typed key space,
ordered delta, existing table installer and two-phase index laws. The finite
service example checks a forbidden intermediate identifier snapshot versus an
accepted complete swap, grouped migration and distinct callback identities.

`traceBindingsWork` counts one overlay read/write per request and at most one
present-replacement conversion. It does not count converter roundtrip primitives
as single machine instructions. Constructing private key spaces, complete
admission, backend operations, wrapper guards, allocation and GC remain charged
separately. Neither a universal equality implementation nor wall-clock speedup is
proved. Persistent carrier, capability equality and explicit bijection laws are
premises, as are stable declared callbacks. No Scheme runtime/compiler proof or
unrestricted callback-termination result is claimed.
