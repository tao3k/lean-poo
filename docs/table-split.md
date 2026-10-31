# Ordered decomposition

This is a finite, explicit extension of the proposed collection library's future
work. It completes the existing table/set `.split` operation across the five
collection styles; it does not infer order or discover a new tree algorithm.

## Protocol and laws

`(.call table .split pivot root)` returns **three values**: a left root, an
`Option Value` at the pivot, and a right root. The sides retain precisely the
original bindings whose declared comparison with the pivot is negative or
positive. Equal comparison must agree with key equality. Comparer totality,
transitivity, purity and persistent backend laws are caller obligations; the
existing comparer checks encountered signs and equality disagreements.

Use `table-order` and an explicit `table-comparer` for a backend that does not
declare `Comparer`. Trie already declares one. No host order is guessed for an
unordered descriptor, and invalid pivots are rejected even on an empty root.
A transported comparer controls visible order, including key-negating Wrappers.

Missing pivot is `#f`; stored false is `(some #f)`. Existing Function wrappers
remain exact admitted leaves. This operation does not normalize children or
attempt to serialize closures. Sets return a Boolean presence observation in
place of the optional Unit payload and retain their own root refinements.

## Atomic ownership and failure

Both sides are prepared from the original snapshot via the existing checked
optional-map protocol. Correlated unique/grouped indexes are reconstructed by
the existing final-state delta installer. Both results must pass complete root
recognition before either escapes. No intermediate remainder must satisfy a
custom refinement, but each final root must satisfy it; some refinements therefore
legitimately reject a split.

Style factories retain declared Comparer identity and dependencies even on raw
backends that omit them from `.sources`. Their union is deduplicated once at
factory construction; retained owners reject revisions, and fresh factories can
explicitly retry against the current declarations.

`table-styles` / `set-styles` lift the operation through their existing multi-result
stage. Pure/Posh retain the predecessor. Mutable/Classy retain its identity as the
left result and allocate a distinct right owner. Linear retires the predecessor
once and supplies two fresh live successors. Receiver calls use `receiver.split`.
The pivot is a non-owning snapshot observation, not a third update capability.

Comparator, metadata, carrier, index or final-root refusal returns no result and
preserves the original owner for explicit retry. A reentrant/competing successful
installation remains visible and rejects the stale outer attempt. Callback side
effects are not rolled back. Persistent leaves are assumed immutable; physical
exclusive ownership is not claimed.

`examples/service-collection.ss` provides `split-ledger-action`: Reader/FUN
prepares both linear successors and the pivot before IO. The regression suite
combines Function invocation, unique-index observations, inverse-delta recovery
and fresh retry with that same action.

## Costs and proof boundary

The reference split makes two checked mapping traversals, plus pivot lookup,
metadata protection and complete input/output recognition. The backend determines
node allocation, delta preparation, index updates, representation conversions and
any ordering/sorting costs. This is **not** a logarithmic split or an allocation
improvement claim. RationalDict now also supplies the existing `number-comparer` to the standard
RBTree bulk and point constructors. Subtraction was invalid there: a large
integer difference or a rational difference need not be a fixnum comparison
result. Bignum and fractional-key controls exercise both construction paths.
The invalid Trie recursion, which confused pivot and traversal
prefix, is removed in favor of the shared checked protocol.

`LeanPoo.Functional.OrderedDictionary` in `TableSelection.lean` proves exact stable
side filters, sign-region coverage and disjointness, late root refusal, preserved
pivot observation, unchanged owner on failure, linear retirement and consumed
input rejection. Backend lookup consistency and lawful comparison are separate
premises: the model's pivot observation is an already admitted lookup in the same
snapshot. `Examples/CollectionStyles.lean` checks opaque callback payloads, stored
false, a transported order and refusal/retry. These finite semantic laws do not
verify Gerbil compilation, locks, arbitrary callback termination, physical memory
ownership or GC behavior.

## Checked single-entry decomposition

The companion `methods.table` now implements the explicit `decons` TODO through
required/optional binding extraction and Set element presentation. All five styles
and their Gerbil receivers reuse the existing single-root installer. Source
admission precedes backend choice; a present choice is one old-value guarded
removal; complete remainder admission precedes the observation and successor.
Required empty extraction preserves the existing Option error, while successful
optional empty extraction follows the same one-step ownership policy.

`TableSelection.lean` supplies finite traversal reconstruction, absence and exact
cardinality without payload equality, guarded chosen-key removal/frame/inverse,
source/empty/remainder failure sequencing and stale-generation refusal through
`installStyle`. Pure/Posh, Mutable/Classy and Linear retain their existing policy.
`Examples/ServiceCollection.lean` checks false versus absent, service-order
reconstruction, required empty refusal and whole-remainder capacity refusal.

The Scheme service example composes correlated indexes and checked Function leaves
with Reader/FUN/IO and inverse recovery. Backend choice order/fidelity, immutable
leaves, stable callbacks and persistent installers are explicit premises. Choice,
guarded deletion, metadata, complete admission and index preparation remain charged;
there is no `.diff` discovery, inferred ordering or destructive storage proof.
This advances the collection proposal's future work without claiming the whole
proposal or automatic algorithm discovery complete.

## Finite traversal prefixes

`(.call table .take count root)` and `.drop` select the first `count` bindings
or their complement in the backend's existing `.filter` visitation order. Counts
are exact nonnegative integers, checked by Gerbil's standard `uint?` contract;
inexact numbers, fractions, negative values and nonnumbers refuse even on empty
input. Oversize counts clamp to the finite traversal. This does not infer a sort
order: an explicit representation's declared traversal determines its prefix.

A single counter predicate delegates to `.filter`. Consequently the existing
Trie structural selection, generic optimistic removals, correlated-index
maintenance and whole-root admission are reused. There is no repeated `decons`,
new snapshot diff or second traversal algorithm. Only complete results must satisfy
custom refinements: a four-entry even-sized family can drop two directly although
the intermediate three-entry root would refuse. Function leaves retain identity.
Set delegates through its existing common `build-set` boundary, keeping Unit private.
Set/style entry points authenticate their input before delegating; no common error
priority is asserted when both the count and the input/owner are invalid.

All five styles reuse the one-root installer; receiver methods are `take`/`drop`.
Mutable/Classy preserve identity, Pure/Posh preserve the predecessor, and Linear
retires it only on success. A successful no-op is still a normal style step.
Invalid counts, rejected final roots and stale metadata publish nothing of their
own; an intervening successful publication wins and the stale outer attempt refuses.
Callback effects and concurrent successful operations are not rolled back.

`drop-ledger-action` composes linear draining with the existing Reader/FUN/IO
observation. Regression controls include both persistent backends, transported
representation order, all ownership presentations, false Set elements, forbidden
intermediate roots, correlated indexes, exact Function identities, inverse deltas,
metadata revisions and reentrant publication. Raw snapshots remain retry inputs.

The counter logic needs constant auxiliary state, but `.filter` may visit the
**entire** source, even for count zero. Full recognition, backend deletion/index
work, preparation and allocation remain charged. No O(count) seek or physical
storage-reuse claim is made. Lean's `prefixBindings` proves take/drop correspondence,
exact reconstruction and cumulative-drop observations without payload equality;
`preparePrefix` proves negative-count, final-refusal and readiness laws. Existing
style installation laws supply consumption and stale-generation semantics. These
finite laws assume faithful persistent traversal and do not verify the compiler,
GC, effectful recognizers or elapsed time. Host noninteger rejection is a Gerbil
contract regression; the Lean count model covers signed integers only.
