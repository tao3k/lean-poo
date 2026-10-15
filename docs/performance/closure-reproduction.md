# Independent Scheme measurements and optional counter comparison

The Scheme package builds, tests and runs its own benchmarks without this
repository. In that package, `just benchmark-closure` produces a Scheme-only
native study using its own scalar oracle. `just benchmark-closure-phases` and
`just benchmark-closure-paired` are also independent. No Lean source list,
checkout path or build-directory layout belongs to those entry points.

## Optional cross-project comparison

`tools/closure-parity.ss` is a research harness owned by this repository. It
compares the 23 deterministic counters; it does not compare CPU or allocation
metrics across runtimes. Native measured values remain observations, separate
from the Lean cost theorems.

Build this repository's `hybridClosureScale` executable using Lake, and build
and install the chosen Scheme checkout in a Gerbil package environment using
its normal `gxi build.ss`. Select that environment with `GERBIL_PATH`. Then run:

```sh
gxi tools/closure-parity.ss \
  "$scheme_executable" "$lean_executable" "$timeout_executable" \
  "$output_file" "$scheme_checkout" "$lean_checkout"
```

All six arguments are explicit. Executables may reside outside their source
checkouts; no `.lake` or Scheme build-directory layout is assumed. Run from any
working directory. Use the package environment built from `scheme_checkout`,
not an unrelated installed copy. Source hashes and executable hashes identify
the selected inputs; hashing alone does not prove source-to-binary provenance.
Toolchain installation and compilation are prerequisites, not measured phases.

The shared Scheme case declaration supplies ten workloads, two seeds, three
scopes, four trials and four queues. Each runtime produces 960 rows. Children
retain the 20-second deadline; Scheme retains its 1 GiB heap bound. The Lean
child has no claimed native heap bound. Failures remain in the output and fail
the run. Common metadata is written once; remaining records are native Scheme
vectors read as data. There is no JSON format or version series.

For source-bound validation after a run:

```scheme
(import (only-in "tools/closure-parity.ss" read-study))
(defvalues (header rows)
  (read-study output-file scheme-checkout lean-checkout))
```

The reader rejects incomplete matrices, duplicate keys, changed definitions,
malformed data, stale selected sources and mismatched counterpart counters.
Previously recorded studies remain tied to the drivers and hashes at their
recorded commits. Use their original drivers when inspecting historical data.

## Recorded control

The [native counter comparison](closure-counter-comparison.scm) completed from
outside either repository with all six paths supplied explicitly: 1,920
observations and 22,080 matching counter fields. Current-source validation
passed; a control with one changed counter was rejected. The standalone Scheme
matrix separately completed 960 observations; its reader refused six controls
(truncated, duplicate, invalid runtime, failed row, extra datum, stale source).
No cross-runtime timing comparison or additional implementation/proof coverage
is inferred from these orchestration checks.

## Typed dispatch and negative extension costs

In the Scheme package, `just benchmark-dispatch` builds and measures independently
of this checkout. `gxi t/dispatch-report.ss <study>` validates its native Scheme
data and reports CPU/allocation medians. It separates signature/index creation,
cold/warm generic calls, negative checking, accepted/refused/canceled patches,
changing guarded values, and heterogeneous family preparation/cold/warm calls.
Source/binary identities and dimension declarations occur once. No new JSON
format or version series is introduced. Use the Scheme PR's fixed
`doc/performance/dispatch-benchmarks.scm` for the recorded observations.

`DispatchExtension.selectCounted_cached` and `observedCounted_result` prove
selection/reference parity and the retained per-candidate work. Recency truncation
and `remembered_comparisons` bound the Scheme association cache to eight shape
comparisons per lookup; equality cost and cache maintenance are separate costs.
Type validation, graph/name resolution, index construction and publication-copy
costs remain visible in the native phases. No constant-time end-to-end dispatch,
zero-allocation call, or compiler/runtime refinement is claimed.

The dispatch report also qualifies allocation-counter admission. A 264-row run
passed semantic checks but produced two negative allocation deltas and was
refused by the reader; its signed native data is preserved in Scheme's
`doc/performance/dispatch-rejected.scm`. The installed runtime's counter was
observed to decrease across GC. Current dispatch rows retain the raw delta and
mark allocation unavailable for every GC-crossing interval or negative delta;
no clamping or selective positive-GC sampling is used. Allocation medians require
all rows in their group to be admitted. CPU/GC observations remain distinct.
Earlier GC-crossing allocation receipts are not retroactively qualified by the
new guard, and no compiler/runtime repair or correctness claim is made.
