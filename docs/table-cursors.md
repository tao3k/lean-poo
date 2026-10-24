# Composed collection cursors

This unit closes a concrete iterator-protocol omission in the collection proposal.
It advances the paper's future work; it does not complete the general collection
library or infer arbitrary isomorphisms.

## One standard protocol

The public `.iter<-` operation returns Gerbil's `Iterator`. Ordered tables reuse
existing `.seek<-` positioning with no lower bound. Indexed tables delegate to
an issued primary snapshot. Representation Wrappers reuse `iterator-map` and
their existing checked key/value translations. No second cursor interface,
namespace or process-specific state is introduced.

A matching declared seek backend keeps its streaming capability through all
three layers. The ordered fallback may still enumerate and sort once when
positioned; ordinary raw backend iterators retain their backend policy. Full
root/cache admission is not removed. This change avoids rebuilding a derived
iteration as a fold/list, not all preparation work.

## Observation and failure laws

- Creating a represented cursor does not translate future bindings. Each pull
  translates the encountered key before its value, preserving checked Function
  identities and stored false values. A present false is distinct from EOF.
- Constructor-owned metadata guards run before every source pull, including
  repeated EOF. Stale origins refuse without advancing the source or translating
  a row. Protection covers the pull and its callbacks, not caller suspension.
- Translation refusal preserves its original cause. The source row has already
  been pulled, so the next pull continues at the following row. There is no
  rewind guarantee for a mutable Iterator. A fresh cursor/request restarts the
  captured immutable root after a transient conversion failure is repaired.
- A later publication through any of the five collection styles changes the
  current owner; an already issued cursor retains its original snapshot. Origin
  metadata invalidation instead rejects that cursor. These are separate events.
- No partial owner update is published by a failed observation. Reader/FUN
  composition permits IO consumption only after the checked observation returns.

## Complete service flow

`examples/service-collection.ss` exports `observe-ledger-first`, composed from the
existing observation map and standard Iterator interface. The cohort regression
combines two correlated indexes, ordered traversal, an explicit representation
Wrapper, Classy publication, a checked Function field and inverse restoration.
A partial team migration is rejected; an atomic exchange succeeds; an issued
cursor still sees the old badges. Invalid Function arguments suppress the IO
consumer; a fresh observation after inverse recovery retains Function identity.

`t/table-cursor-test.ss` also covers streaming without fold/list fallback,
per-row conversion order, active/empty/exhausted invalidation at each derived
layer, exact conversion refusal and restart, and snapshots across all five
styles. Fixtures reuse the existing `box-table` constructor with ordinary Gerbil
keyword defaults.

## Formal scope and cost

The companion Lean `TableObservation` laws reuse `checkedTablePull`. They prove
stale refusal with unchanged unread rows, key-before-value conversion, exact
refusal after source advancement, EOF guarding, opaque payload preservation and
agreement with eager mapping at a successfully demanded head. `CollectionStyles`
instantiates these laws with the service cohort, owner publication, failure,
fresh retry and present false.

Work counts are source pulls and entry translations: stale `(0,0)`, current
nonempty `(1,1)`, current EOF `(1,0)`. Entry translation includes separately
specified recognition/inverse checks. The counts do not include guard scans,
root/cache admission, allocation, construction, GC or scheduler time. Backend
snapshot fidelity, supported metadata writes and supplied translation laws are
premises. Runtime/compiler correctness and arbitrary callback termination are
outside this finite model. No wall-clock speedup is claimed from these counts.
