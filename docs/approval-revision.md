# Approval revision changes during competing submissions

This advances finite generalized-prototype future work from the original Racket
Appendix B lens/wrapper construction (`$lens-gen`, source pin
`9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133). The paper does not
specify a concurrent metadata transaction system. Existing graph revisions, bounded
whole-SCC closure, lawful lenses, FUN Reader actions and native objects are reused.

## Installation and policy revision share one lock

Previously the final metadata guard check preceded acquisition of the head
installation lock. The coordinator now checks those captured guard revisions
INSIDE that same lock. `component-publication.revise-approval!` performs one
ordinary native constant-slot update under the coordinator lock, preserving the
head and advancing the native object's revision. It does not introduce a second
metadata representation, a callback-based transaction or a global revision number.
Every concurrent write to these registered approval objects must use the same
coordinator. Cross-coordinator writes, raw mutation, custom reentrant mutation
hooks and hidden dependencies remain outside the protocol.

If a coordinated policy edit precedes installation, old guard versions refuse.
If installation precedes the policy edit, that publication was admitted at its
installation point; the edit affects subsequent requests and does not revoke an
already published historical snapshot automatically. Head identity and approval
version are separate checks. Changing a policy value away and back still leaves
old guards stale. Revision equality is never inferred from equal policy values.

`examples/component-requests.submit-current!` explicitly prepares fresh current
snapshot/guard captures and submits once. It does not retry automatically, rebase
fragments, reuse denied candidate caches or choose a topology phase for the caller.
After a rival changes topology, the caller selects the corresponding new phase.

## Complex native controls

`approval-revision-test` exercises five scenarios using existing service examples:

- Three siblings staged on one head all refuse before builders after an approval
  change and change-back. Fresh staging succeeds on the unchanged head.
- Two worker threads pause after whole closure and successful approval. One
  service is revoked; a newly staged request refuses. The policy is restored and
  a fresh third request publishes spare=5/settlement=30. Both paused old requests
  then refuse and return that exact current winner.
- Only approval metadata changes while an approved worker is paused, with NO
  rival publication. Its installation refuses, proving the metadata check matters
  independently of head comparison. Fresh current-policy staging can later succeed.
- An attempted policy write from inside a protected approval refuses before the
  object changes. Standard lock cleanup allows subsequent update and publication.
- Six topology transitions each stage three siblings under one service refusal,
  preserve the exact current head, then freshly stage after current-policy update.
  Late siblings refuse. Independent feedback receipts remain identical throughout.

Standard bounded channels schedule the worker interleavings; waits and joins stay
at five seconds inside the existing 90-second focused gate. These controls do not
prove exhaustive thread schedules or arbitrary mutable-object safety. Production
component computations and approval callbacks remain pure and locally total;
coordinator writes are explicit policy-management effects.

## Formal correspondence

`Functional.ComponentPublication.installChecked` augments existing head arbitration
with abstract captured/live revision equality. The revision type can describe the
combined versions of several heterogeneous services. Proofs establish metadata-only
stale refusal, accepted exact candidate/head/approval/revision, retry after fresh
capture on an unchanged head, and that ANY finite list of candidates captured at
one obsolete approval revision leaves the current head unchanged, in any order.

`Examples/ApprovalRevision.approvalCheck` builds and closes actual merge/split source
recipes using `ComponentExecution`. Three staged candidates fail after two-service
revision drift/change-back; joint refusal preserves current; fresh capture succeeds;
late siblings preserve its head; a current-topology split then closes and installs.
Fixture identity/version numbers are local to Lean and never loaded by Gerbil.

Faithful native revision increments, complete registered metadata, fresh publication
identity and correct lock behavior are implementation premises. The proofs model
serialized decisions, not C++/compiler/runtime verification. Fixed finite lawful
lens families, correct declared reads, accepted graph certificates, immutable
component descriptors and faithful builders remain premises. No arbitrary-effect
rollback, general convergence/leastness, hidden dependency inference, speed or GC
claim. No new versioned JSON, full benchmark data or archives are committed.

The initial aggregated example exceeded its unchanged 30-second check (exit 124).
Shared source/recipe definitions now live in `LeanPoo.Examples.ComponentRounds`,
and the executable controls are split by scenario into `Examples/ComponentRounds`,
`Examples/ComponentRequests` and `Examples/ApprovalRevision`. The intermediate
combined rounds/requests run also timed out (exit 124), so both prior scenarios
remain separate mandatory checks rather than reducing coverage. All three retain
the original 30-second per-check bound; no failed run was converted into a pass by extending
its timeout. Fixture extraction does not change source equations or gate coverage.
