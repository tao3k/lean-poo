# Checked table selection across persistent backends

This closes a concrete omission in the collection proposal's future work.
Trie previously implemented public `.filter` and `.partition` directly and treated
any non-false predicate result as true. The common implementation admitted Bool
but rebuilt from `.empty`, unnecessarily requiring transient roots and pointwise
index updates. Neither behavior is the shared checked selection protocol.

## Shared boundary and existing algorithms

`methods.table` owns both public operations. `select-table` stays in the existing
`clan/poo/table` module, alongside the other bulk algorithms in `table/mapping.scm`.
It checks the predicate procedure even for an empty input, admits the original
root before callbacks, requires each decision to be Bool, and recognizes every
complete returned branch before exposing a result. Recognition does not normalize
or rewrap child Functions. Callback/type/refinement failures retain their causes;
callback effects are observable and are not rolled back.

Declared `.filter/key` and `.partition/key` capabilities retain Trie's existing
structural algorithms and unchanged-subtree sharing. They receive a checked
classifier. Public `.filter`/`.partition` are inherited, so specialized traversal
cannot accidentally bypass the common admission boundary. Direct capability use
is an internal backend obligation, not an additional checked entry point.

A generic table folds the original root once, records ordered removals, and calls
the existing `.apply-delta` once per changed branch. All classifier decisions
precede either install; no predicate is replayed. A no-op branch returns the
original root and makes no persistent writes. No empty seed or admitted
intermediate deletion root is required. Final roots must still satisfy the full
descriptor; an inadmissible empty result is a real refusal.

Explicit `table-wrapper` representations transfer the complete source selection
operation and encode its outputs. They do not replay point removals through an
indexed receiver. Source and target refinements and encountered inverse checks
remain in force. Traversal remains the source fold order, including a representation
whose key mapping reverses numeric order; it is not silently resorted.

Correlated indexes prepare deletions against each final primary through their
existing delta installer. The complete source primary is recognized before any
index cache preparation; carrier-only delta shape admission cannot substitute
for the source descriptor's whole-root refinement. Unique/grouped cache entries and all declared origins
remain synchronized. Source/backend shape, persistent-write fidelity, finite
distinct-key traversal and declaration stability remain protocol obligations.

## Ownership, composition and failure retry

The five existing styles use the same single-result step or multi-result stage.
Both partition branches are private until admission and one owner commit finish.
Mutable/classy retains the first owner identity and creates a separate second
owner; linear retires its predecessor only on success. Refusal leaves the original
owner live; reentrant/competing winners and stale metadata retain their existing
rejection semantics. No extra transaction, scheduler or namespace is introduced.

`partition-ledger-action` and the existing set `partition-access-action` share one
higher-order Reader/FUN operation. Complete branches are observed before the IO
consumer runs. The service example routes indexed callback-bearing rows, refuses
an incomplete cohort without invoking IO, then explicitly restages a fresh
classifier and preserves every checked Function leaf.

## Formal and executable acceptance

`t/table-selection-test.ss` retains its independent finite oracle and adds strict
Trie/generic callback controls, original-root-before-callback refusal, final-root
refinements, no-insertion/no-op write counts, indexed representation transfer,
all five styles, late second-root refusal and the complete FUN/IO service retry.

`TableSelection.lean` proves input/classifier/second-output refusal order, owner
retention on late failure, deletion lookup/frame and no-op laws without Function
equality, the combined deletion count and representation transfer preserving
branch order and exact errors. Top-level `Examples/CollectionStyles.lean` checks
four opaque callback-bearing services, incomplete-cohort refusal, successful
restaging and approval refusal after preparing the first branch.

The Lean view laws assume faithful backend observations and lawful representation
translation. The deletion count is at most one edit per original binding across
both partition branches; it is not an allocation or wall-time bound. Admission,
backend lookup/write, index projection, conversion and GC costs remain explicit.
Arbitrary callback termination, destructive backends, automatic symmetry discovery
and compiler/runtime verification remain outside this finite unit.
