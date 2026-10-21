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
not proved by the abstract delta equations. General key/value-changing
isomorphisms and maintained aggregates remain future work.
