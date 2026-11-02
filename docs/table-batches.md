# Ordered persistent revision batches

The finite collection work now includes one composable ordered-batch protocol.
The Scheme `methods.table` `.compose-deltas` operation returns an ordinary delta,
so existing installation, inverse, isomorphism transport, retractable folds and
FUN consumers can use it without a new collection hierarchy.

`LeanPoo.Functional.OrderedDictionary` in
`LeanPoo/Functional/TableBatch.lean` supplies these laws:

* `batchChanges_correct`: flattened installation equals sequential execution,
  including the first failing key, without a unique-key premise.
* `batchChanges_append` and `batchChanges_associative`: grouping preserves the
  exact ordered edits and intermediate expectations.
* `batchChanges_inverse` and `applyBatches_inverse`: reverse-order undo restores
  every original observation after successful installation.
* `transport_batchChanges`: explicit key/value isomorphisms preserve composition;
  existing transport/install laws preserve results and mapped conflict keys.
* `foldChanges_append` and `applyFold_batch_error`: intermediate contributions
  remain ordered and a complete admission failure produces no aggregate state.
* `batchChanges_length` and `batch_foldWork_bound`: total edit count and the
  existing two-contributions-per-edit projection bound.
* `batch_stampMatches`: every captured origin remains required, including origins
  belonging to requests with no writes.

`Examples/TableRevision.lean` combines repeated updates, deletion/reinsertion,
temporary services, shared opaque callback handles, late conflicts, failure retry,
aggregate undo and explicit representation migration. It also shows why cancelling
writes cannot be replaced by an empty revision on a stale base.

The corresponding Scheme regression covers RationalDict and Trie, admitted
Function identity, stale provenance, snapshot-scan refusal during composition,
late conflict before projections/consumer IO and retained live key ownership after
reinsertion. Transport now maps intermediate optional values rather than looking
up both sides only in the endpoint snapshots. Paired-fold ownership removes a key
only if it is absent from the completed staged table.

Theorems concern finite observations with explicit lawful representation and
aggregate premises. They do not prove Scheme execution, callback termination,
compiler/runtime correctness, GC cost or concurrent publication. Composition does
not infer sequential compatibility without a base: the existing installer checks
it. No global snapshot/ABA protection or edit coalescing is claimed. This closes
the ordered batch unit, not the proposed whole general collection library.

`pruneDeletedOwners_live` proves that a live final key keeps its collision owner,
regardless of earlier deletions. The ordered grouping regression also guards the
standard concatenation boundary: use order-preserving `map` and `append`.
