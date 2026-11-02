# Simultaneous SCC revision and shared dependency migration

This advances Appendix B's generalized-prototype future work. Racket's lens
getter/setter/wrapper construction remains the component semantics; SCC regrouping
and joint revision form a new compositional layer around those existing equations.

`Functional.GraphRevision` adds typed dependent batches on existing finite node
support. A checked revision has distinct code/base targets, all supported by the
source. Successful admission preserves the submitted payloads. Application proves
actual writes (including explicit absence), unchanged support and exact resolver
equality for unedited components. This is the source-side premise of selective
reuse, separately from graph invalidation and closed-result equality.

The SCC revision laws combine independent seed sets without losing readers,
propagate any number of membership changes, and invalidate consumers of a migrating
shared member even if consumer code/representative names/projected values stay
unchanged. The converse no-seed law proves the graph condition for services detached
from an obsolete source. Actual reuse also needs resolver equality and existing
ConstructionCache/FeedbackCache laws; a pointer hit alone is not mathematical proof.

`Prototype.ComponentClosure` factors complete component families through the
existing generalized lens compiler. Its residual theorem covers every member of
an actual returned group. `Examples/ServiceRevisions` uses twelve vector positions:
quota/spare/shared, six endpoints, unchanged monitor, joint settlement and an
independent loop. One transition splits `(shared a b)`, moves shared into `(shared
c d)`, merges `(e f)` and switches shared from quota to spare. It also exercises
quota edits in the same batch, reversal, equal-valued migration, detached old-input
and new-input invalidation, actual bounded closure/residual checking and current
joint admission. The final typed batch's actual resolvers are checked against the
constructed values. Its representative visit order is dependency-first for these
fixtures; native condensation uses the existing checked DAG scheduler.

Native `generalized-graph.revise` stages all edits before reconstruction.
`feedback-graph-revision-action` is FUN bind over the SAME old publication; guards
cover preparation through final admission. `component-group-builder` captures lens
identities once, registers every read lens/extra source, checks per-component
provider locality and closes the whole raw carrier with every residual. The older
component-services example reuses this abstraction too. Native controls verify
builder skipping, exact independent receipts, unchanged monitor reconstruction,
refusal of a partial service edit, retry after speculative work, explicit missing
inputs, duplicate/unsupported batches and guarded preparation writes. Preparation
or admission failure returns the exact old publication.

Proofs establish the stated typed source/group/invalidation laws. Concrete example
runs and native object identity checks are separate controls; no verified Scheme
extraction or compiler/runtime theorem is implied. Finite accepted graph
certificates and pure/local-total callbacks, declared reads, lawful immutable lens
storage and faithful builders remain premises. Arbitrary convergence/leastness,
hidden callback dependency inference and cycle-interior selective recomputation
remain outside the result. Functional closure is prioritized here; there are no
new performance claims, versioned JSON, full benchmark data or archives. Gerbil
requires no Lean checkout or serialized witness.
