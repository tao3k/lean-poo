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

## Element-level collection styles

`set-styles descriptor` derives `Pure`, `Mutable`, `Linear`, `Posh` and `Classy`
from a `Set<-Table.` presentation. It stays in `clan/poo/table` and calls the same
private derivation engine as `table-styles`. There is one reference type, capture
operation, immutable-head conflict check and installation path; no second owner,
lock, scheduler or conversion adapter is introduced.

The constructor checks `descriptor.Elt` is the backing `Table.Key` and the backing
Value is the standard Unit descriptor. The style protocol's `Domain` is the set
Type. Both backing recognition and the set's possibly stricter `.element?` are
required at admission and after every staged transformation. A broad custom
predicate cannot bypass carrier admission; a narrow predicate cannot be bypassed
by operating through the backing table. Declared `.sources` on the set and the
backing table's origins are retained together. Revisions to any of them invalidate
old protocols and cursors, including EOF.

```scheme
(def styles (set-styles RationalSet))
(def classy (.@ styles Classy))
(def current (.call classy .ap admitted-permissions))
(def grants (.call classy .ap admitted-grants))
(@@method current.union grants)
(def next (@@method current.cons permission))
(def elements (for/collect (element next) element))
(def sum (@@method next.foldl + 0))
```

All five protocols supply `.elt? state element`, `.cons element state`,
`.remove state element`, `.union/.inter/.diff/.symdiff left right`, and
`.subset?/.disjoint?/.=? left right`. Binary operands are states of the same
protocol/family; conversion or explicit pure-snapshot admission is required to
cross owned families or styles. Pure snapshots remain shareable.

A binary update captures the right snapshot, then stages and commits only the
left capability. Pure/posh returns a successor and retains the old state;
mutable/classy returns the same updated identity; linear retires the left aliases
and returns a new capability. A distinct right owner is observed, not consumed.
If both operands alias the same capability, successful owned retirement applies
to every such alias. These are single-left-owner commits, not atomic publication
of two independently mutable owners. Reentrant/competing updates still use the
original head comparison. No callback is placed under the head lock.

All 25 conversions retain the exact admitted persistent set root and wrapped
Function elements. The existing FUN `.admit` boundary normalizes raw elements;
`.ap`, operations and conversions recognize admitted values without wrapping them
again. Inserted elements must already be admitted (validate a new Function before
`.cons`, or use explicit `.admit` on a raw snapshot). Pure recognition cannot
establish that an arbitrary raw procedure already has its Function wrapper.

`.list<-`, `.iter<-`, `.foldl` and `.foldr` expose elements, not `(element . Unit)`
entries. Folds use `(element accumulator)` callbacks. Posh/classy reuse Gerbil's
existing Iterable registration. Ordered `.seek`, `.seek<-` and `.range` delegate
to the backing table and project keys only; comparator direction, bounds, errors
and positioned traversal are unchanged. No ordering capability is inferred for
an unordered source. Retained cursors observe their captured root after ownership
transfer, but source metadata remains checked at every pull and EOF.

Set `.diff` remains set difference; backing `Table.diff` remains ordinary delta
discovery. `.apply-delta` and `.apply-batch` use those existing table deltas in every
set style, including inverse recovery and all original conflict/metadata rules.
`access-style-action` in the existing service example composes grants/revocations,
classy updates, linear transfer and a final posh receiver through Reader/FUN into
an IO consumer. Intermediate owners are local to the action. Failure suppresses
that consumer; retry explicitly starts from an admitted root, without replaying
external effects automatically.

`LeanPoo/Functional/SetStyle.lean` proves the binary update delegates to the existing
style engine, exact backend refusal preserves independent owners, right ownership
is retained, style changes leave results unchanged, and all 25 transfers preserve
the carrier. Element fold and cursor proofs preserve order, opaque Function key
identity, pull counts and EOF metadata refusal without requiring equality of
functions. The preparation theorem retains ownership when specialized output
recognition refuses. The top-level set example extends the same access revision
chain; no new example namespace or Scheme checkout dependency is required.

Regression controls cover the conversion matrix, four operations in every style,
nonconsuming relations, standard Iterable/fold, owned and aliased retirement,
foreign/retired operands, explicit retry, declared set origins, stricter custom
recognizers, positioned element queries, Function wrapper identity, batch/inverse
and Reader/IO suppression. Admission and backend merge costs remain visible;
this feature does not assert destructive storage reuse or wall-time improvement.
