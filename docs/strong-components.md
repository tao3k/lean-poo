# Checked SCC discovery and feedback revisions

This is a scoped advance of the original generalized-prototype future work in
Appendix B. Its Racket `$lens-gen` supplies the getter/setter/wrapper component
semantics; automatic grouping is an additional graph layer, not an assertion of
an already specified SCC algorithm in the paper.

`LeanPoo/Functional/StrongComponents.lean` computes finite bounded reachability,
then checks reflexivity, inclusion of each edge and transitivity. Sound computed
paths plus these checked laws prove that every accepted relation is exactly the
unbounded graph path relation. `Checked.members` therefore describes exact SCC
membership and `no_quotient_cycle` excludes mutually reachable distinct groups.
The general theorem that every finite input passes discovery is not supplied.

Revision seeds combine body edits, SCC membership changes, and added/removed
reads. Proofs establish propagation through all new-graph transitive readers,
atomic dirtiness within an SCC, and that a clean node has no path to any seed.
Changes in values alone do not justify retaining a merged/split group. These
are graph-side laws: actual reuse also needs resolver equality and the existing
ConstructionCache/FeedbackCache closure laws. Registered mutable sources must
still be guarded; an identity hit is not a new mathematical proof.

`Examples/ComponentServices.lean` executes the same five equations as the native
example: shared quota, mutually dependent left/right services, downstream joint
settlement and an independent self-loop. It discovers memberships, constructs
actual generalized lens fragments, closes each group with budget 32 and checks
all component residuals. Both merge/split directions dirty services/settlement,
while shared input edits spare the independent loop. Universal vector lens laws
are proved separately. The fixture supplies a dependency-first representative
visit order; production Gerbil uses the existing checked DAG scheduler. Current
joint approval is exercised with accepted, overcommit and revoked-permission
cases, alongside the existing generic approval theorem.

Native `strong-components.ss` computes exact visited reachability; its
`feedback-graph.ss` adapter condenses groups and composes the existing FUN Reader,
whole-group closure, cache and joint admission. Resolver reuse checks complete
memberships, member code/base identities, external footprints and ownership.
ConstructionCache can now retain independent slots across support changes;
new slots always build and unsupported reads still fail scheduling. Native tests
check actual skipped builders/object identities, refusal retaining exact old
publication, retry reconstruction, divergence and unavailable inputs. The native
package does not read this checkout, and these checks do not verify the runtime.

Arbitrary convergence/leastness, hidden closure dependency inference, cycle-
interior selective rebuilding and performance laws remain outside this result.
Immutable/extensional metadata, pure locally total callbacks, correct declared
reads and faithful group builders are premises. Raw search budgets exclude SCC
analysis, residual evaluation, cooking and approval costs. No new benchmark data
or serialized proof/JSON artifacts are required for this functional increment.
