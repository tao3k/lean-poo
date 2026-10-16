# Competing requests with local and joint admission

See [joint-installation.md](joint-installation.md) for opaque post-approval receipts,
installation races, registered shared-policy drift and fresh staging after refusal.

This extends generalized-prototype future work, reusing original Racket Appendix B
`$lens-gen` (source `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133),
existing declared graph revisions, lawful lenses, whole-SCC closure and FUN actions.
The paper does not specify this multi-service transaction protocol.

## Admission composition

`Functional.JointPublication.admitted` combines every declared endpoint check
against ONE candidate bundle with its independent joint predicate. `prepare`
retains the explicit expected identity and complete candidate in the existing
request type. `admitted_iff` separates both obligations; `joint_refused` proves
that a failed joint relation preserves the complete current bundle regardless of
local results. `run_denied_prefix` proves a stronger compositional consequence:
removing a jointly denied prefix leaves the result of ANY finite remaining
request sequence unchanged. A denial cannot consume a valid sibling's freshness.
`run_denied_between` extends this to any position in an arbitrary finite trace;
`admitted_endpoint` extracts the actual check of any declared endpoint member.
Existing stale-batch and validity laws cover later competing publications.

The native example exports `joint-approved?` and accepts a higher-order `joint:`
predicate at construction. The default remains the shared total budget. Service
admission continues to use the existing component equations, support checks and
proposed shared/local policies. Callers can compose additional pure family
relations with the default predicate. `joint-publication` already invokes this
predicate only after every local revision action has succeeded; installation
still uses one guarded whole-snapshot pointer, not independent endpoint writes.

## Concrete interleaving

The native controls stage multiple requests from the same actual snapshot:

1. A's bridge insertion/SCC merge produces A=24, B=12. Shared local ceiling=24
   admits both endpoints, but total budget=35 refuses the whole candidate twice.
   A pre-staged budget=36 sibling still succeeds; other old siblings become stale.
2. A deletes B/D and splits while service B inserts E/F and merges: A=16, B=24.
   Local ceiling=24 passes both, budget=39 refuses. Explicit fresh staging with
   budget=40 succeeds. A separately staged valid A-only replacement then fails
   as stale, along with the earlier winning request.
3. A restores B/D/removes E/F while B deletes B/D/splits: A=12, B=16.
   Local ceiling=16 passes, budget=27 refuses. A pre-staged budget=28 sibling
   succeeds without implicit rebasing. B then restores compact support, returning
   values/ceiling/budget to 12/12, 12/24. All earlier requests remain stale.
4. Fresh current-snapshot preparation again adds A's bridges and succeeds.

Both independent `stable` feedback receipts retain exact native identity through
the round trip; deleted E/F have no current receipt. Another control sets the local
ceiling to 12 for A=24: it refuses before the joint callback, preserving a valid
same-round sibling. Diagnostic test callbacks record the actual joint candidates
and independently rerun both complete endpoint admission predicates. This makes
local-success/joint-failure observable, rather than attributing every exception
to the joint budget. Diagnostic log mutation is test-only, not a production purity
or rollback claim.

`Examples/JointAdmission.lean` uses shared certified topology heads, retaining
actual source declarations, discovered support/SCC graphs and successful component
resolver equations. Its first two refusals explicitly assert every local check
true and joint check false, then run competing request lists, source round trips,
stale replays and fresh restaging. The native third-round 27/28 control extends the
same generic law. Shared fixture code lives in `LeanPoo/Examples/JointTopology`;
focused executable controls remain separate under their original 30-second limit.

## Scope

The endpoint list must enumerate the complete family; declared dependencies and
lens laws must be correct. Finite key families, accepted graph certificates,
immutable policies/descriptors, fresh installed identities and faithful pure
locally total builders/callbacks remain premises. Native readers capture one
bundle. Lean proves the serialized whole-bundle semantics; native controls execute
actual closures and immutable snapshot identity. This does not prove arbitrary
effect rollback, distributed/durable atomicity, general recursive convergence,
interior-SCC incremental solving, runtime/compiler correctness or performance.
