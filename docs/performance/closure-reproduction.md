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
