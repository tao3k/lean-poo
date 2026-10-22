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
Automatically inferred conversions remain future work.

## Delta-driven folds

`foldl_correct` proves a general optional-write law sufficient for arbitrary
accumulators: the complete fold after one write must equal a sparse step using
the actual old optional binding. No group structure is inferred for user code.
The concrete `contribution`/`foldView`/`foldStep`/`foldChanges` construction uses
exact integer contributions; `foldView_replace` derives the write law from a
unique finite inventory containing every updated key. `foldChanges_correct` and
`applyFold_correct` prove sparse/full agreement and unchanged first-conflict
refusal. `foldChanges_inverse` proves accumulator restoration. Full reference
folds, sparse steps and complete source/aggregate installation commute with the
existing explicit key/value bridges (`transport_applyFold`), pulling scores back
through their inverse maps.

`foldWork_bound` counts at most two projections per supplied edit. It excludes
initial scans, shape admission, equality, backend writes, descriptor preparation,
metadata lineage, arithmetic, allocation and GC. The model makes no wall-clock
or general O(delta-count) workflow claim. In particular, isomorphism conversion
still scans both snapshots, and Trie shape admission may scan its structure.

Gerbil `table-fold` uses the existing Wrapper and `.zero/.add/.sub` protocol.
Its opaque state retains the admitted source alongside its aggregate; `.unap`
recovers that source rather than inverting a lossy numeric total. Initial `.ap`
performs full recognition/folding. `.apply-delta` completes old-value/origin
checks before any aggregate callback, then returns the privately staged source
and sparse aggregate together. `.get` and `.unap` enforce owner and metadata
freshness, including converted delta origins retained through empty/inverse
updates. FUN composition suppresses the consumer on failure and permits retry.
Pointwise count/weighted-sum examples retain shared checked Function handles.
The regression compares 24 rounds on each RationalDict/Trie carrier with an
independent sum and forbids accidental fold enumeration during sparse updates.

The proof premises include stable admitted values, pure successful operations,
backend refinement and the optional-write law. Exact integer sums are proved;
product metrics satisfy the law coordinatewise. Arbitrary floating-point or
order-sensitive folds are not covered by the retractable law merely because
methods exist. Runtime type checks and metadata guards are tested controls,
not universal proofs of arbitrary Scheme callbacks, external effects, concurrency
or termination. The examples remain in top-level Examples/TableRevision.lean.
