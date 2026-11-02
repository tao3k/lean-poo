# Multi-round component revision and joint approval

This advances generalized-prototype future work. Original Racket Appendix B
`$lens-gen` (source pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines
2108–2133) supplies the getter/setter/wrapper and delayed inheritance construction.
It does not specify SCC revision transactions or general convergence. Lean and
native Gerbil compose that construction with existing graph, bounded closure,
source discipline and cache laws.

## Revisions staged against a publication

`component-revision.revision-action` stages service fragments against the exact
live expected graph-cache object. Existing native FUN Reader bind threads that
same current input to the existing joint graph revision action. A different
publication refuses BEFORE reading contributions, building groups or approving.
The captured object remains live; no numeric revision counter, structural-value
comparison, serialized identity or Lean checkout is used by Gerbil.

This matters after a round trip: a component can be removed and later recreated,
so old staged fragments may satisfy membership freshness again. Equal current
values or the same supported names do not authorize an old request. Callers may
explicitly prepare a fresh action against the new publication. The unanchored
`reconfigure` API still intentionally applies contributions to its supplied source;
snapshot validation is explicit in the staged workflow, not silently added there.

Native publication identity is an operational premise of the Lean abstraction.
`SupportRevision.joinAt` uses an abstract decidable snapshot type; proofs show
stale requests refuse, matching identities delegate to ordinary joint validation,
and acceptance implies BOTH the requested identity and checked joint edits.
The example's natural-number labels are local proof-fixture identities. They are
not imported or hardcoded into Scheme and do not establish runtime freshness.

## Interleaved practical scenario

`examples/component-rounds.ss` and `Examples/ComponentRounds.lean` share the
existing twelve-position lens family and actual component recipes:

1. Compact support starts with `(shared A B)` and `(C D)`, shared capped by quota=3.
2. Add E/F bridges, merge both SCCs, migrate shared to spare=4; settlement becomes 24.
3. Delete B/D, retain/rewrite E/F, split into `(shared A E)` and `(C F)`; settlement is 16.
4. Delete E/F, explicitly recreate B/D, restore BOTH surviving A's read footprint
   and the shared quota input; settlement returns to 12.
5. Add E/F and merge again with spare=5 in the same batch; settlement becomes 30.
6. Delete B/D and split again; settlement becomes 20.
7. Restore B/D, remove E/F and revise quota=2 in one batch; settlement becomes 8.

Unchanged monitor and settlement invalidate across the current condensation graph.
An independent feedback group's exact receipt survives all rounds; builders for
untouched inputs/groups refuse if invoked. A separate standard `foldl` control
runs three complete merge/replace/restore cycles, threading each actual publication
as the next expected snapshot. Reader bind is used WITHIN a round; it is not
misused to thread changing publication state across rounds.

Both service policies approve the same fully closed candidate every round. A
later service refusal retains the exact last publication. After policy metadata
changes, old captured lens checks remain invalid: retry must prepare a fresh
request against the retained graph and CURRENT policy versions. Tests verify this
rather than weakening the source guards. Fresh no-op requests skip constructors
but still check current joint policy. Writes to guarded policy objects during
construction refuse; this does not imply rollback of arbitrary external effects.
Partial restoration leaving A's read of removed E refuses before builders and
approval. Deleted providers remain absent and replacement providers are explicit.

## Shared reference execution and proof limits

`Functional.ComponentExecution` factors the prior source-driven numeric example
runner into a reusable finite-vector construction. It accepts any homogeneous
value type with decidable equality, uses the existing functional lenses and whole
group closure, and computes edges from ACTUAL typed source recipes. `Closed`
retains every successful source equation for every active key. Universal vector
lens laws and `resolved_correct` prove that missing/error providers cannot be
approved by a totalized bounded search. `ComponentMigration` now reuses this runner.

The fixtures visit representatives in a dependency-first source order. The reference
runner checks matching support and final real residuals; it does not prove arbitrary
orders complete. Native production continues to use the checked condensation DAG
scheduler. Every successful group checks all component residuals. Existing
support-aware invalidation, whole-SCC rebuilding, conditional clean reuse, erased
providers and current approval laws apply separately on each accepted transition.
Executable checks cover exact alternating groups, dirty sets, complete outcomes,
repeated construction and support/value round-trip refusal. Native pointer controls
are distinct from formal source equations and abstract identity proofs.

The range remains accepted finite graphs with correct declared reads, fixed
lawful lens families, immutable/extensional descriptors, pure locally total
callbacks and faithful builders. General convergence/leastness, hidden dependency
discovery, cycle-interior skipping and unrestricted knots remain TODOs. No runtime,
compiler, speed, allocation or GC theorem follows. Functionality precedes performance
work. No new versioned JSON, full benchmark data or archives are committed.

See [component-publication.md](component-publication.md) for authoritative head
arbitration between competing staged requests and retry after joint refusal.
