# Persistent table revision semantics

`LeanPoo/Functional/TableRevision.lean` extends the existing
`Functional.OrderedDictionary` namespace with finite optional-binding deltas.
This advances the paper's future collection-library work, reusing dictionary
observation and lens laws rather than claiming a new construction in the paper.

The completed unit includes:

* finite discovery completeness for a unique key inventory covering all differences;
* sequential application and exact first-conflict refusal;
* inverse restoration after successful installation and an untouched-key frame law;
* a total optional-binding lens, including absent keys and stored false;
* a `TableCarrier` refinement: lookup after a backend write must equal optional
  replacement in the existing observation model;
* cross-carrier delta transport retaining successful observations and exact errors.

`Examples/TableRevision.lean` combines deletion, false-valued insertion, conflict
at a later edit, rediscovery/retry, service metadata and composed lens laws.
Gerbil `methods.table` implements the same ordered optimistic operations with its
existing RationalDict and Trie backends. Its `examples/service-collection.ss`
connects proposal admission and installation to Reader/FUN and IO consumption.
Its existing collection regression module includes 48 revisions against an
independent alist oracle and recursive Function-wrapper retention.

The Gerbil discovery order is source updates/deletions followed by target-only
insertions; the Lean inventory abstracts that order. Discovery scans snapshots;
application accesses only changed bindings after carrier admission. Empty deltas
return the original Scheme table. These are source-level operation facts, not
measured speedups or allocator/GC claims.

The backend lookup/write law, descriptor equality, stable admitted values and
pure backend operations are assumptions. Opaque callback handles can model
procedure identity; no extensional equality procedure is derived. Gerbil's actual
tree runtime, collector, compiler, arbitrary callback termination and concurrent
publication are not verified by this model. Scheme has no Lean dependency.

Conflict checking concerns changed keys, allowing unrelated edits to rebase. It
is not global revision fencing and does not reject ABA at equal bindings. Scheme
separately refuses captured descriptor revisions; those runtime guards are tested,
not proved by the abstract delta equations.

## Explicit key/value conversion

The next completed unit reuses `Prototype.DictionaryBridge` for explicit typed
bijections. `transportView`, `transportChange` and `transportChanges` lift those
to observations and ordered deltas. Proofs establish key injectivity, optional
expectation equality reflection, complete view/edit roundtrips, undo commutation,
finite discovery commutation, write commutation and installation commutation on
both success and the exact first mapped conflict key.

Gerbil's existing `Wrapper.` `.ap/.unap` and `methods.table` implement the same
protocol. `table-isomorphism` takes explicit source/target table descriptors and
key/value Wrappers with matching Domain/Codomain. Its `Delta` Wrapper converts
`(admitted-base . delta)` pairs, installing the origin first and converting both
snapshots through one target-backend collision registry. This rejects aliases
across deleted/inserted keys as well as within either snapshot. Edit order and
origin/converter metadata lineage are preserved. Failures expose no partial result;
FUN composition suppresses the IO consumer and allows rediscovery/retry.

Both inverse laws, preservation of admitted values, pure stable callbacks, and
agreement between backend equality and the logical observation model are premises.
Runtime recognition/roundtrip checks are finite controls, not a universal callback
proof. Reordering already admitted Tuple/Pair Function leaves preserves their exact
procedure identities without wrapping again; arbitrary raw callbacks are not made
safe by membership recognition. The Lean service example uses opaque callback
handles, shared services, deletion/insertion, conflicting publication and inverse
recovery. It does not prove Scheme procedure semantics or arbitrary termination.

Conversion includes complete snapshot scans, original delta installation, private
carrier construction, registry lookups and metadata checks; it is not O(edits) in
general. No runtime performance improvement is inferred from these algebraic laws.
Automatically inferred conversions and maintained aggregates remain future work.
