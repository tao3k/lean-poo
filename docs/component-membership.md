# Support changes, SCC regrouping and joint admission

This is a finite generalized-prototype future-work extension of Appendix B's
Racket getter/setter/wrapper construction. Active component support changes before
existing lens-based whole-equation closure and current service admission.

`Functional.SupportRevision` reuses typed dependent batch edits on a source whose
bindings are restricted to the intersection of old/final support. Proofs establish
exact final keys, both provider namespaces erased outside support, actual resolver
absence for deleted nodes, fresh defaults independent of latent old values, and
exact resolver equality for unedited survivors. Actual writes reuse the previous
Revision laws. Existing old snapshots remain immutable.

`Functional.SupportedComponents` separates a finite key/lens universe from current
active nodes. Distinct support and closure of EVERY declared active read are
checked before masking. Path lifting/forgetting proves that accepted active groups
are exactly SCCs of the original declared graph. Inactive positions have no group.
This matters for a new isolated node: its full-universe SCC was already a singleton,
so ordinary unmasked membership comparison would miss the insertion. Support-aware
membership seeds prove every new active node dirty, propagate to current readers
and exclude removed slots from materialization. Conditional resolver equality,
correct builders, group equations and current approval remain separate laws.

`Examples/ComponentMembership` matches the native twelve-position carrier with
only ten positions initially active. Adding E/F bridge components merges `(shared
a b)` and `(c d)` into one SCC and moves shared to spare. Removal plus rewiring
splits the SCC, optionally with a quota edit in the same batch. The example runs
actual existing component lens closure/residual checks and tests dirty sets,
isolated insertion, dangling-reference refusal, latent-base erasure, fresh explicit
re-addition and admission. Its representative order is dependency-first for these
fixtures; production Scheme uses the checked condensation scheduler. Custom vector
lens laws hold universally; executable runs and native pointer controls are
separate evidence.

Native `graph.reconfigure` stages final support and updates together, reusing
`graph.revise` and the existing FUN Reader revision/publication boundary. It clears
removed providers and prevents unsupported old bindings from reappearing on
addition. Legacy support-view and provider-removal APIs keep their earlier meanings.
Native controls also cover unchanged monitor reconstruction, skipped independent
builders, deleted SCC representatives getting fresh surviving group keys, denied
insertion/retry, partial deployment and current policy-only revocation. A missing
new definition or dangling read cannot publish, and failures retain exact old state.

The proof range is accepted finite graphs with correct declared dependencies,
pure locally total callbacks, lawful immutable lens storage and faithful builders.
The example uses a declared lens universe; supporting a new key outside a builder's
family requires a suitable builder, rather than automatic lens discovery. Arbitrary
convergence/leastness, cycle-interior skipping and unbounded universe evolution
remain outside this increment. Raw closure budgets do not include graph analysis,
residual work, cooking or admission. Functional closure precedes optimization;
there are no performance claims, versioned JSON, full run data or archives. Scheme
has no dependency on a Lean checkout or serialized proof.

The reference SCC checker now materializes its finite reachability relation once
in standard immutable vectors before checking the same laws. Vector lookup is
proved to expose the original computed relation, retaining reachable_sound and
all accepted-certificate guarantees. The expanded example passes the unchanged
30-second check bound after this change; the initial unshared run timed out and
remains a failed diagnostic, rather than a relaxed gate or a native speed claim.
