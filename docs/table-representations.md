# Table algorithm derivation through representations

`LeanPoo/Functional/TableRepresentation.lean` extends the existing
`LeanPoo.Functional.OrderedDictionary` namespace. `TableCarrier.conjugate` constructs
a new table's read/write operations from an existing lawful persistent carrier and
explicit key, value and carrier `DictionaryBridge` isomorphisms. The target needs
no second data-structure algorithm.

The fifteen laws cover:

* Lookup and write correspondence without a snapshot scan.
* Whole delta and ordered batch execution, with exact carrier results and mapped
  first conflicts; repeated keys require no uniqueness premise.
* Inverse installation and inverse derivation of the original algorithms.
* Composition of multiple representation derivations for both read and write.
* Left/right fold order, exact binding count and binding roundtrip.
* Complete captured-source and converter revision admission.

Root `Examples/TableRevision.lean` combines negated integer keys, Tuple/Pair
rearrangement, a host metadata field, shared abstract callback handles, deletion /
reinsertion, temporary services and a late conflict. The Scheme implementation
`table-wrapper` reuses `methods.table`, FUN `Wrapper` / `Wrap`, Gerbil records and
existing source backends. It supports ordinary collection algorithms, lenses,
recursive normalization, delta transport and incremental aggregate states.

The explicit bridges carry universal inverse laws in Lean. Scheme checks actual
encountered counterexamples and captures supported metadata dependencies; it does
not infer universal laws or invisible mutable closure state. Original table laws,
stable callbacks, conversion and equality costs remain explicit premises.
Negated keys retain source enumeration order; no independent numerical sorting or
comparator certification is asserted. No allocation/GC or compiler correctness
claim follows from the finite operation correspondence.

This closes explicit representation-driven algorithm derivation, a concrete unit
of the general collection TODO. Automatic discovery of arbitrary symmetries,
linear/mutable API generation, optimization synthesis and the whole general
collection library remain separate work.

Nested generated protocols publish complete `.sources` metadata. Existing delta,
fold and isomorphism construction closes over those origins, so changing an inner
converter invalidates outer aggregate reads and even empty deltas. The nested
source-guard law includes every origin. The Rational Pair decoder now accepts one
Pair, matching ordinary `compose`, and JSON encoding first converts the Rational
to its Pair. Regression controls cover signed exact fractional byte/JSON roundtrips;
the generic codec theorem assumes the underlying codec law and does not prove a
JSON parser or arbitrary numeric normalization.
