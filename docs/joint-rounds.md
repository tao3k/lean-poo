# Interleaved atomic joint revisions and fresh preparation

This extends finite generalized-prototype future work from original Racket
Appendix B's lens/wrapper construction (`$lens-gen`, source pin
`9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133). It composes the
existing graph/whole-SCC closure, lens guards, FUN revision actions and atomic
joint-bundle publication. The paper does not specify this transaction protocol.

## Preparation captures the same expected bundle

`joint-publication.stage-at` accepts an explicit captured snapshot. It rejects a
stale snapshot before inspecting contributions, then prepares the same immutable
replacement policies and endpoint edits as the existing `stage`. `stage` delegates
with the currently captured snapshot. Neither function rebases old calculations.

`stage-with` reads current ONCE, passes that exact bundle to a higher-order pure
preparation callback, and uses standard `call-with-values` to receive the two
contribution streams. It then calls `stage-at` with the same expected bundle.
If another publication won during preparation, staging refuses. A competitor may
still win after the staging check; the existing submit/install checks then refuse.
This is optimistic preparation, not a lock held across callbacks or an automatic
retry loop. A new invocation explicitly recomputes from current source and metadata.

`examples/joint-services.stage-current` uses this hook to derive a new shared POO
policy from the current native policy object and stage both endpoint phases. Other
policy fields remain inherited. Installed/proposed metadata and contribution lists
retain the existing immutable/extensional discipline. Hidden callback dependencies
need explicit guards; arbitrary external effects cannot be rolled back.

## Complex native controls

Four new scenarios use actual existing service graphs and closure:

- Two complete merge requests pause after approval while a third whole request
  publishes. Both resumed requests refuse and return the exact winner. Subsequent
  split and restore publications return to old field values; all original requests
  remain stale because the snapshot object changed, even with equal fields.
- Preparation reads old policy state, then an explicitly scheduled competitor
  publishes. `stage-with` refuses that old calculation. Fresh current-topology
  preparation succeeds. A stale `stage-at` rejects before malformed edits are read.
- Six merge/replace/restore transitions each prepare a denied joint candidate and
  a sibling, preserve all current fields on failure, then freshly compute and install
  a complete candidate. Both earlier requests are stale after each success. Stable
  independent feedback receipts retain exact identity for BOTH endpoint heads.
- A policy-only successful bundle retains endpoint values but still invalidates
  staged siblings. Explicit fresh preparation then publishes the intended merge.

Standard channels/joins retain fixed five-second bounds inside the existing
90-second focused gate. Pausing/scheduling callbacks are explicit test effects;
production preparation, construction and approval callbacks remain pure/locally
total. These bounded schedules are distinct from exhaustive SMP/runtime verification.
All readers project metadata/heads from ONE captured authoritative bundle.

## Formal correspondence

`Functional.JointPublication.stale_batch` proves that ANY finite sequence of old-
expected submissions preserves a different current bundle, regardless of candidate
payloads, order or approval flags. Field-value round trips do not weaken identity.
`Request` and `run` compose the existing whole-bundle installation decision over
arbitrary expected identities. `run_valid` proves joint validity through every finite
interleaving if the initial bundle is valid and every approved candidate is valid.
Per-step `whole`, refusal, stale retention and complete commit remain unchanged.
Actual constructors/residual checks and truthful joint admission establish validity
separately; fresh native identity and faithful locking remain premises.

`Examples/JointRounds` closes actual compact/merge/split/restore recipes through the
shared `ComponentExecution` runner. It checks competing candidates, denial and fresh
commit, restored equal fields with a new identity, late batch refusal and a newly
prepared merge from the restored source. Fixture identities are local Lean inputs;
Gerbil does not load Lean source or serialized proof values.

Scope remains accepted finite graphs, correct reads, fixed lawful lens families,
immutable metadata and faithful pure locally total builders. No arbitrary-effect
rollback, hidden-dependency inference, convergence/leastness, interior-SCC skipping,
crash durability, compiler/runtime correctness or performance claim. No new
versioned JSON, full benchmark data or archives are committed.
