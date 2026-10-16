# Joint component contributions and shared migration

This advances the original generalized-prototype future work. Appendix B's
`$lens-gen` composes getter, setter, wrapper and delayed inherited computation;
it does not specify an SCC mutation or transaction algorithm. The implementation
reuses those lens constructions, existing finite closure, immutable graph edits,
checked SCC discovery, DAG caching and current approval.

## One final source from several services

Lean `Functional.ComponentRevision.RevisionFragment` and native
`component-revision.Fragment.` contribute `added`, `removed`, `codes`, `bases`.
`SupportRevision.join` / native `reconfigure` flatten each namespace in submission
order. Removed keys must be current, added keys fresh, and both membership lists
must be distinct across ALL contributions. Deleting and re-adding the same key
in one publication refuses. An endpoint replacement therefore names distinct old
and new keys; a normal recipe replacement edits code without changing membership.
A repeated membership batch is stale and refuses rather than silently overwriting.

Surviving old keys retain their order, followed by ordered additions. The existing
support revision erases removed providers, clears latent providers on fresh keys
and validates code/base target support and duplicate writes. Code and base are
independent namespaces; equal duplicate payloads still conflict within a namespace.
Conflicting revisions have no implicit last-writer precedence. No sorting or
commutativity claim hides the ordering of support or SCC representatives.

Cross-service references may point to components added by another contribution.
Only the final source is partitioned, closed and approved. A partial contribution
with a dangling read refuses before builders or approval. A final supported key
without a provider cannot close. Native publication uses the existing FUN Reader
revision boundary and source/lens guards, preserving the exact old publication
on preparation, construction or admission failure. No partial service state is
published and a refused candidate never becomes the retry cache.

## Complex alignment scenario

The shared twelve-position lens universe starts with only ten active components.
Independent contributions remove B/D, add E/F, replace the two old SCCs `(shared
A B)` and `(C D)` with `(shared A E)` and `(C F)`, and move shared's cap from quota
to spare. One service deliberately reads E/F before their supplying contributions
appear. The second SCC reads the first group's closed shared value. Monitor's
recipe remains unchanged but its receipt must rebuild. Settlement jointly checks
all four current endpoints. Quota, spare and independent stable feedback receipts
retain exact identity and their refusing builders are skipped.

Both examples close actual equations to 4, then to 5 after a new shared input.
An additional mixed batch changes both inputs to 9/5 while replacing both SCCs,
with exactly one approval of the final native candidate. Subsequent old-quota
changes rebuild only quota; spare changes invalidate both current SCCs, monitor
and settlement. Tests also cover provider erasure, duplicate code/base and membership
contributions, stale replay, policy denial/retry, missing providers, and no-op
contributions that skip builders but still require current approval.

Lean discovers edges from the ACTUAL typed submitted recipes. The numeric closure
search evaluates those resolvers, totalizing errors only during bounded search;
a separate final residual checks that every active resolver returns exactly its
successful candidate value. `resolved_correct` proves that the residual cannot
approve a totalized error. This avoids a detached arithmetic model. Native retains
its existing error-preserving computation and whole-component builder directly.

## Proof and execution boundaries

Generic Lean proofs establish accepted exact fields, exact support membership,
unique writes across contributions, erasure of both removed provider namespaces,
and fresh defaults independent of latent old definitions. Existing survivor-frame,
support-aware dirty propagation, conditional clean reuse, whole-group equations,
current admission and universal vector lens laws compose with those results.
The example checks actual accepted SCC memberships, dirty sets, source outcomes,
closures and policy decisions. Native pointer and refusing-builder controls check
the implementation's cache behavior separately from those formal laws.

This remains a fixed finite key/lens family with accepted graph certificates,
correct declared reads, faithful builders, immutable/extensional descriptors and
pure locally total callbacks. Descriptor mutation is not made safe by a cache hit;
callers supply registered source guards when using mutable metadata. No claim of
arbitrary convergence, leastness, dynamic lens discovery, external-effect rollback
or interior-SCC selective reconstruction is made. Lean's fixture visits a valid
dependency-first order for these sources; native uses its checked DAG scheduler.
Functionality precedes optimization: no runtime speed/allocation claims or new
benchmark corpus are included. Gerbil runs independently of the Lean checkout;
no proof constants, versioned JSON, full run data or archives are stored here.

See [component-rounds.md](component-rounds.md) for repeated component recreation,
interleaved merge/split, current cross-service approval and snapshot-bound staging.
