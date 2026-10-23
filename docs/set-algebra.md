# Finite set algebra over existing tables

This closes a concrete collection-library unit in TODO.md and advances the
[collection proposal](https://github.com/fare/projects/issues/10), part of the
prototype paper's future work. `Set<-Table.` already presented table keys as set
elements. Its difference operation omitted its operands, equality called a
nonexistent backend method, and the general presentation lacked subset and
disjointness. These were implementation gaps, not automatic algorithm-discovery
or destructive-storage research questions.

## One existing interface

`Set<-Table.` stays in `clan/poo/table`; `table/sets.scm` is a standard compiler
include tracked by `defbuild-script`. The set's `Table.Value` must be the standard
`Unit` descriptor. The carrier stores an admitted element as a key and `(void)` as
its value. The algebra uses existing backend merge, short-circuit traversal and
membership operations; it does not create a new tree, set engine or namespace.

| Operation | Membership rule |
| --- | --- |
| `.union a b` | In either operand. |
| `.inter a b` | In both operands. |
| `.diff a b` | In a and absent from b. |
| `.symdiff a b` | In exactly one operand. |
| `.subset? a b` | Every member of a belongs to b. |
| `.disjoint? a b` | No member of a belongs to b. |
| `.=? a b` | Mutual subset, independent of backend value equality. |

`RationalSet` and `SimpleTrieSet` retain their existing representations. The Trie
subset specialization retains its shared-subtree shortcut inside complete
admission. Merge callbacks and backend traversal keep their existing order;
extensional commutativity does not imply a new order for materialized lists.
Subset/disjointness do not construct a merged carrier. Equality uses membership
in both directions, not extensional equality of callable elements.

`.compare` remains an explicit backend ordering capability. A backend without it
raises `unsupported set comparison`; set membership alone does not certify an
order. The finite algebra is not a new generic sorting policy.

## Admission and failures

Every algebra/relation operation admits both operands before backend work, even
for empty or identical inputs. The `with-set-tables` scope uses existing table
origin closure and construction protection. It recognizes admitted values without
normalizing them, preserving exact Function key wrappers. Invalid carriers or
children raise the existing TypeError. A non-Unit backing descriptor raises
`set algebra requires Unit values` before merge. Inputs remain persistent.

Backend errors retain their original causes and no partially merged result is
returned. External callback effects are not rolled back. Supported descriptor
writes are refused throughout the operation. A backend that captures another
mutable descriptor in a closure must list it in `.sources`, following the existing
table protocol; hidden mutable state is not inferred or certified. No operation
caches approvals or silently replays a failed callback. Explicit retry runs against
current admitted operands; retained table deltas keep their original revision and
changed-key conflict checks.

## Boolean membership lens and whole revisions

`.lens element` now uses the project's `lens-of-get-set` constructor and its
value-before-state setter convention:

```scheme
(def focus (.call set .lens element))
(def added (.call focus .set #t admitted-set))
(def nested (.call Lens .compose (.lens access) focus))
(def changed-service (.call Lens .modify nested not service))
```

Both lens accessors admit the carrier and recognize the element without wrapping
again; the setter uses Gerbil's Boolean contract. False deletes membership, true
inserts the standard Unit payload. The get/put, put/get and last-put-wins laws
compose with existing service lenses and preserve unrelated fields. The convention
is corrected directly, with no reversed-argument compatibility path.

Set `.diff` means set difference. The existing backing `Table` retains `.diff` as
ordinary table-delta discovery. There is no second set-delta representation:

```scheme
(def desired (.call set .diff (.call set .union before grants) revoked))
(def changes (.call (.@ set Table) .diff before desired))
```

`prepare-access-revision` in `examples/service-collection.ss` prepares that complete
policy once and returns the existing Reader/FUN installation-plus-IO action.
Revocation wins over simultaneous grant. The action can install on a current
snapshot; a changed expected key refuses before the IO consumer. Retry explicitly
captures against the winner. The same Unit-valued delta transfers to a compatible
Trie, supports whole-batch/style publication and uses `invert-table-delta` for
reverse recovery. Backend representation and logical Key/Value compatibility
remain the original delta protocol's premises.

## Proofs and checks

`LeanPoo/Functional/SetAlgebra.lean` models membership as `K → Bool`, encodes it as
`K → Option Unit`, and proves all four optional merge selectors refine pointwise
set semantics. Backend merge/lookup laws are explicit premises. Finite enumeration
completeness gives subset/disjointness, and mutual subset gives extensional
equality without requiring decidable equality of Function keys. The module proves
union/intersection commutativity, union idempotence, difference partition,
symmetric-difference cancellation, revocation precedence, subset transitivity,
disjointness symmetry, ordinary delta completeness/inverse and membership-lens laws.

Top-level `Examples/SetAlgebra.lean` composes access grants/revocations, finite
revision completeness over every key, first-conflict refusal, explicit retry,
classy failure retention, inverse and a service membership lens. The public Lean
entry imports the module so standard CI producer builds include its artifact.

Scheme regressions exhaust every pair of four-element subsets on RationalDict and
Trie against an independent list-membership oracle (512 operand pairs). Additional
controls cover malformed/identical/empty operands, Unit refusal, Function wrapper
identity, original backend error identity, declared-origin mutation refusal and
retry, lens laws and type errors, cross-backend delta installation, linear reverse
recovery, competing publication refusal and IO suppression.

Admission may scan the operands, and generic merge performs backend lookups and
persistent writes; no constant-time/sublinear or wall-time improvement is claimed.
Finite laws do not verify Gerbil's tree implementation, structural equality,
procedure extensionality, exception-safe foreign resources, GC or scheduling.
Destructive backend reuse and automatic symmetry discovery remain separate scope.
