# Table algorithm derivation through representations

`LeanPoo/Functional/TableRepresentation.lean` extends the existing
`LeanPoo.Functional.OrderedDictionary` namespace. `TableCarrier.conjugate` constructs
a new table's read/write operations from an existing lawful persistent carrier and
explicit key, value and carrier `DictionaryBridge` isomorphisms. The target needs
no second data-structure algorithm.

The sixteen laws cover:

* Lookup and write correspondence without a snapshot scan.
* Whole delta and ordered batch execution, with exact carrier results and mapped
  first conflicts; repeated keys require no uniqueness premise.
* Inverse installation and inverse derivation of the original algorithms.
* Composition of multiple representation derivations for both read and write.
* Left/right fold order, exact binding count and binding roundtrip.
* Complete captured-source and converter revision admission.

Root `Examples/TableRevision.lean` combines negated integer keys, Tuple/Pair
rearrangement, a host metadata field, shared abstract callback handles, deletion /
reinsertion, temporary services and a late conflict. The Scheme implementation
`table-wrapper` reuses `methods.table`, FUN `Wrapper` / `Wrap`, Gerbil records and
existing source backends. It supports ordinary collection algorithms, lenses,
recursive normalization, delta transport and incremental aggregate states.

The explicit bridges carry universal inverse laws in Lean. Scheme checks actual
encountered counterexamples and captures supported metadata dependencies; it does
not infer universal laws or invisible mutable closure state. Original table laws,
stable callbacks, conversion and equality costs remain explicit premises.
Negated keys retain source enumeration order; no independent numerical sorting or
comparator certification is asserted. No allocation/GC or compiler correctness
claim follows from the finite operation correspondence.

This closes explicit representation-driven algorithm derivation, a concrete unit
of the general collection TODO. Automatic discovery of arbitrary symmetries,
destructive backend optimization, optimization synthesis and the whole general
collection library remain separate work.

Nested generated protocols publish complete `.sources` metadata. Existing delta,
fold and isomorphism construction closes over those origins, so changing an inner
converter invalidates outer aggregate reads and even empty deltas. The nested
source-guard law includes every origin. The Rational Pair decoder now accepts one
Pair, matching ordinary `compose`, and JSON encoding first converts the Rational
to its Pair. Regression controls cover signed exact fractional byte/JSON roundtrips;
the generic codec theorem assumes the underlying codec law and does not prove a
JSON parser or arbitrary numeric normalization.

Pair JSON decoding delegates to both child descriptors, including the existing
integer-string and nested-container codecs. Exact rationals with 80/100-bit
components and nested Pair/List controls cover that boundary; `pair_codec_roundtrip`
retains the separate child-codec premises. Raw JSON children are not returned as
though they were already decoded values.

Pair child decoders run explicitly left to right; a left failure preserves its
original cause and suppresses the right decoder, as checked by an effect trace
and the corresponding ordered Except example.

Serialization requires existing child codecs. Opaque Function closures remain
unsupported on the wire; no closure serialization is inferred from membership.

Pure/mutable/linear style derivation is now closed for admitted persistent tables;
see [table-styles.md](table-styles.md) for ownership, failure and observation laws.

Declarative correlated index installation is now available over the same persistent
backends and styles; see [table-indexes.md](table-indexes.md) for its laws and scope.

Explicit ordering is a separate law-governed extension: `table-comparer-wrapper`
transports a declared comparer through the key isomorphism, and `table-order`
derives ordered folds and finite ranges without guessing host numeric order.
See [table-order.md](table-order.md) for bounds, invalidation and cost premises.
Explicit backend seek now transfers through the same Wrappers when a source
advertises it and the caller shares its transported Comparer. Automatic ordering
discovery and private backend tree inspection remain outside this unit.

## Backend cost acceptance

The bounded acceptance unit is the complete source/derived-representation
workflow over the existing persistent RationalDict and SimpleTrie backends.
`just benchmark-collections 64 10 6` retains all earlier phases and adds six
`backend-{rational,trie}-{cold,workflow,retry}` phases. It uses the existing shared
`test-program`, standard `defbuild-script`/`std/make`, and Gambit process statistics;
there is no alternate loader, scheduler or companion Lean checkout.

Warm routes share the admitted source descriptor and immutable base with the same
Function leaves; no mutable installation state crosses sides. Cold routes create
fresh protocols. Cold includes fresh source/derived descriptor preparation, full source-backend
materialization from the same input rows and carrier admission. Warm setup is reported separately, never mislabeled cold.
Every operation captures an optional edit, checks old-value equality, installs,
observes **every** binding and invokes the shared checked Functions, then installs
the inverse and checks the restored total. Retry first refuses a stale request on
a competing snapshot, restages against that snapshot, publishes, and undoes back
to the competing snapshot. No consumer is reached through a refused installation.
The source is a reference for the same admitted abstract observations, not an
implementation of the derived protocol's extra runtime inverse/metadata checks.
Its elapsed time is therefore not an expected upper bound on a checked wrapper.

The measurements include carrier/key/value conversion, structural `equal?` on
newly reconstructed Tuple/Pair values, descriptor preparation, child membership,
guards, persistent reads/writes, full observations, undo, allocation and GC.
Diagnostic converter/public-protocol-read/write/fold counters run **outside** timed observations;
counts are invocations, not constant-time cost assertions. Equality time remains
inside full CPU/wall measurements: it is not inferred by subtracting two noisy
microbenchmarks or by assuming `equal?` is constant-time.

Pairs alternate AB/BA, with the existing independent A/A and B/B controls,
identical fixed prefixes, natural and collected GC histories, complete signed
allocation/GC fields and all adverse samples. Separate old/new linked-program
ABBA observations use the same newly compiled workload and source fixtures. Only
compact receipts belong in Git; raw observations and executable copies stay out.

### Local sharing of checked carrier conversions

A four-closure prebinding experiment was rejected: its cold CPU differences did
not establish an improvement and sometimes increased. It is not shipped.
`table-wrapper` instead reuses the recovered/encoded intermediate **within one**
carrier check. Both encountered inverse comparisons, membership, traversal order,
source/receiver guards and stale revision refusal remain. Encode now invokes
wrap/unwrap 2/1 times instead of 2/2; decode invokes them 1/2 instead of 2/2.
No global cache, closure factory or cross-call memo is added. The premise is the
existing pure, stable converter law; this does not certify arbitrary effects of
repeated callbacks. A changing converter is still subject to both encountered
inverse tests and its counterexample is refused in the regression suite.
The FUN example `revise-ledger-point` stages once and publishes only after checked
installation. Regressions combine malformed replacement, suppressed consumption,
Function identity, conflict, ownership/style conversion, explicit retry and undo.

### Proof and evidence boundary

The companion `TableCarrier.applyCost` follows the existing installer's actual
successful prefix and first conflicting key. Its arbitrary state/edit-dependent
quote can include read, comparison, conversion and backend costs. `applyCost_add`
and `conjugate_cost_overhead` retain every additive category; `applyCost_conflict`
charges the failed comparison without charging a write or unexecuted suffix.
`tableWorkflowCost_breakEven` requires the complete extra preparation/observation
cost to fit within an installer's saving. The local-sharing law preserves both
short-circuit inverse comparisons for pure converters, without assuming constant
conversion or equality costs. Concrete late
conflict and negative total-cost controls live in root `Examples/TableRevision.lean`.

These are finite persistent semantics and conditional work-accounting laws, not
machine timing, arbitrary callback termination, VM/GC/compiler verification, or a
universal guarantee that a generated wrapper is faster than its source backend.
Unknown source-specific complexity and arbitrary payload equality/conversion costs
remain explicit quotes. Automatic optimization/symmetry discovery is a research
boundary; it is not required to close this bounded backend acceptance.

### Local matched receipt, 2026-10-23

Darwin arm64; Gerbil `1cfb032`, Gambit `ea114fc`; 64 input bindings,
10 operations/sample, six alternating pairs plus four A/A and four B/B controls
per phase/regime. Every old/new process runs the same **22 phases** and all
semantic oracles. An ABBA old/new linked-program comparison supplies 12 matched
cross-version observations per backend phase/regime; same-version cross-run
controls retain six. Old program SHA256 starts `77b2b6e8e642`, candidate starts
`20ff15312e3b`; the source baseline is Gerbil PR #13 commit `82588bb`.

Candidate-minus-old wall medians, microseconds per complete operation (positive
means slower; no adverse sample or phase is omitted):

| Workflow | Natural | Collected |
| --- | ---: | ---: |
| RationalDict cold construction/publication/undo | -44.98 | -29.15 |
| RationalDict prepared publication/undo | +1.66 | +5.73 |
| RationalDict conflict/restage/retry/undo | -31.84 | -44.42 |
| Trie cold construction/publication/undo | -5.84 | -10.24 |
| Trie prepared publication/undo | -41.91 | -59.70 |
| Trie conflict/restage/retry/undo | +21.49 | -19.97 |

The RationalDict prepared natural/collected cross-run A/A wall ranges were
-35.69..+558.30 / -52.07..+72.10 us; B/B ranges were
-145.22..-30.90 / -287.10..+1522.09 us. Its adverse collected +5.73 us
row has CPU +2.10 and non-GC CPU +5.25 us. Trie natural retry retained CPU
+15.80, GC CPU +31.00 and non-GC CPU -5.70 us; A/A wall ranged
-45.39..+337.41 and B/B -102.31..+116.21 us. Medians of separate categories
need not add. These controls do not establish a substantive new regression,
**nor a stable universal wall improvement**; GC/history and signed residuals remain
in the raw evidence. The earlier admitted-base-only four-closure diagnostic retained cold CPU
increases (+169.40/+293.40 us RationalDict natural/collected); it was withdrawn,
not relabeled a successful optimization.

Carrier callback attribution is deterministic for both backends: cold 60→45,
prepared workflow 52→39, retry 80→60 calls, a **25% reduction in carrier calls**,
not in all conversions, allocation or elapsed time. Key/value conversion counts
and public protocol read/write/fold invocations are unchanged. Counters do not
count every internal tree primitive or constructor allocation. Both inverse
comparisons remain and the regression suite checks the 2/1 and 1/2 directions,
foreign-carrier refusal before converters, and a failing right inverse.

The guarded derived representation still costs more than the admitted raw source.
In the candidate's first run, cold/prepared/retry natural premiums were
1196.79/991.69/1243.02 us for RationalDict and
1221.72/854.06/1003.74 us for Trie; collected premiums were
1248.31/985.25/1284.41 and 1310.15/820.64/974.00 us respectively.
This includes the runtime typed conversion/inverse/metadata checks absent from
the raw source reference. It is a measured cost, not a zero-cost derivation claim
or an unqualified interchangeable raw path for untrusted inputs.

Complete shared-study entry wall times in ABBA order were
31.32 / 27.73 / 27.54 / 28.61 seconds. The balanced new-minus-old mean is
-2.33 s, while old A/A differs by -2.71 s and new B/B by -0.19 s.
The first old startup alone took 2.632 s wall versus 0.017/0.016/0.014 s
in the remaining runs. Thus an entry-wall speedup is **not established**.
Cold protocol materialization is measured inside a loaded fixed-prefix runtime,
not claimed as process-cold compilation. All preparation/build commands retain
standard scheduling and the existing compiler/heap/stage limits.

Final full local acceptance: Scheme 128 modules / 1,263 cases in one process,
normal exit 0 under 1 GiB / 300 s; Lean all 343 atoms and every full-gate phase,
including supervision, diagnostics and document checks. Six new conditional laws
and three concrete cost controls use the existing namespace and root examples.
Only this compact summary is versioned; raw runs, statistics and binaries stay
outside Git. CI continues to run the complete suite and all study phases.

## Guarded child Type selection

The private translation directions retain the four admitted child Type identities
inside the existing revision scope. This replaces repeated unobserved `Key` and
`Value` demands with record-field selection; it creates no additional converter
closures. Compatibility, membership, inverse comparisons, collision checks and
origin guards remain in the complete workflow. Preparation includes the extra
record fields and all four initial child demands.

When slot-read observation is active, conversion still uses the actual live
metadata getters. This preserves access refusal and current dependency reads;
no cached value stands in for access authority and no read token is fabricated.
Regressions cover exact denial causes, stale read provenance, replacement of a
child Type, child mutation during conversion, empty-delta refusal and fresh
rebinding after revision.

The shared study retains every earlier phase and adds preparation, complete
observation and structural-equality diagnostic slices for both backends. Workflow
and retry also retain post-GC inclusive controls. Equality fixtures preserve the
same Function identities and include both equal and unequal reconstructed values.
These slices locate costs; subtracting their noisy timings is not a measurement
of equality time inside the complete workflow. Complete wall/CPU/GC observations,
AB/BA order, A/A and B/B controls and all failures remain authoritative.

The Lean model proves captured/live transport agreement under explicit identity
agreement, stale-dependency rejection, observed-getter denial preservation and
prefix-cost scaling. Its break-even law charges complete extra preparation
against repeated selection savings, with cold and GC-premium negative controls.
It assumes externally justified cost quotes and does not prove Gerbil allocation,
GC scheduling, machine timing or speedup from field-access counts.

### Local paired receipt: guarded child selections

The old linked program is `ad206b8`; the candidate captures child identities in
its two existing direction records. Both execute the identical 28-phase workload
with 64 bindings, 10 operations, six AB/BA pairs and four A/A plus four B/B pairs
per phase/regime. Each of four process runs completes all 195 summaries and exits
0 under the unchanged 1 GiB / 300 s limits. No build runs overlap measurements.
The linked programs have distinct SHA-256 identities (old `20ff1531…f54fc`,
candidate `e9a1a3d9…ff9e1`); raw observations and binaries remain outside Git.

Below are **new minus old**, microseconds per complete operation, with 12 matched
cross-version observations per cell. Negative is faster. Natural/collected columns
are wall medians; non-GC and GC columns are separate natural CPU medians and do
not necessarily add to the wall median.

| Backend / phase | Natural wall | Collected wall | Natural non-GC CPU | Natural GC CPU |
| --- | ---: | ---: | ---: | ---: |
| RationalDict cold | -349.86 | -182.31 | -205.90 | -44.30 |
| RationalDict workflow | -131.60 | -148.94 | -107.50 | -16.75 |
| RationalDict retry | -164.84 | -143.29 | -136.15 | -34.20 |
| Trie cold | -144.20 | -101.09 | -122.70 | -18.15 |
| Trie workflow | -141.24 | -178.90 | -84.65 | -40.85 |
| Trie retry | -118.21 | -110.20 | -121.40 | -15.90 |

Both workflow natural and collected cells improve in all 12 cross-version
observations. Natural workflow ranges are [-185.73, -51.69] us RationalDict and
[-524.50, -12.11] us Trie. Same-version natural workflow A/A medians are
+61.50/-144.95 us and B/B -2.29/-96.64 us respectively: drift remains material.
Other cells retain adverse samples. In particular Trie natural retry ranges from
-336.69 to **+2157.40 us**. That worst batch has CPU -66.60 us and GC CPU
+69.40 us per operation, with two collections on both sides. Most of its elapsed
regression is therefore wall-minus-CPU residual, not an increase in measured CPU;
this does not identify the external cause or justify removing the sample.
The collected Trie workflow range also retains a -8540.11 us extreme.

Preparation alone has natural medians -0.20/+6.31 us (RationalDict/Trie), with
non-GC CPU +3.10/-6.70 us; it has no stable standalone speedup. Complete observation
natural medians are -51.64/-33.10 us. The independent equality control changes by
+0.012/-0.036 us: no equality algorithm changed, and this control is not subtracted
from workflow timing. Conversion checks, equality and metadata refusal remain.

Charging forced collection **plus first call plus batch**, divided by all 11 calls,
gives workflow/retry medians -85.99/-332.79 us RationalDict and
-49.86/-159.71 us Trie. Workflow maxima remain +72.18/+56.51 us and Trie retry
+610.46 us. This synthetic control does not promise production GC latency.

Complete entry wall seconds in ABBA order are 36.10 / 34.32 / 32.34 / 33.88.
Balanced new-minus-old is -1.66 s, while old A/A changes by -2.22 s and new B/B by
-1.98 s. Thus these measurements support the bounded workflow improvement but
**do not establish a stable full-entry speedup or eliminate latency variance**.
Final local Scheme acceptance is 128 modules / 1,265 cases in one process;
Lean full acceptance retains all 343 atoms, stress, supervision and document gates.

## Receiver scopes and entry accounting

Wrapper guards reuse the complete receiver/source scope prepared after private
construction, instead of allocating its leading pair for every operation. All
instantiation, revision-map equality and metadata checks remain in place. A nested
call reuses the standard existing scope-identity fast path only when its complete
active list is identical; partial overlaps retain the existing protection path.

A separate candidate replacing revision-map equality with Gerbil's two-list
`andmap` was withdrawn after complete paired measurement. Length and proper-list
checks were essential for refusal semantics, but temporary-list removal did not
produce complete-workflow speedup. Its reference equivalence law remains a
semantic control, not an assertion that the runtime uses that candidate.

Regressions revise each of six independent origin positions, reject old reads and
empty deltas, and reject derived-receiver writes inside FUN and fold callbacks.
The receiver revision and original snapshot survive refusal. Lean proves complete
receiver/origin coverage and, for the withdrawn comparison candidate, exact
agreement of the paired predicate with complete mapped-list equality, including
short/long mismatches. A signed wall-residual law makes the empirical premise
explicit: CPU savings imply wall savings only when residual growth fits within
them. A negative control models lower non-GC and total CPU with higher wall time.

The existing full study measures the unchanged fixed prefix through its shared
Gambit statistics helper and reports the entire loaded entry, including diagnostics,
setup, prefixes, measured calls, GC and output. Startup is separate. These totals
are not inferred by adding medians. Raw boundary histories retain GC wall/CPU,
collection counts, allocations, heap/live history and adverse observations.

### Paired receipt: retry tails and prepared receiver scopes

The reference is linked `e55e57a`. Both experiments execute the identical complete
28-phase study: 64 bindings, 10 operations, six AB/BA pairs plus four A/A and four
B/B pairs, all 195 summaries per process. Four processes run old/new/new/old with
unchanged 1 GiB / 300 s bounds. No local builds overlap measured runs. Raw results,
failed attempts and binaries remain outside Git. No forced GC is added to natural
observations and no adverse sample is removed.

**Withdrawn revision-list candidate.** Proper-list and length checks plus public
Gerbil two-list `andmap` preserve mapped-list equality only with structural scalar
equality. The first numeric-equality prototype failed the existing malformed-state
regression; correcting the implementation retained its stale-error expectation and
added improper-list controls. The corrected full suite passed, but performance did
not justify adoption. Trie natural retry wall median was +1.06 us, RationalDict
workflow +18.49 us. Loaded-entry mean regressed +2.289 s: CPU +0.425 s (non-GC
+0.281, GC +0.144), residual +1.864 s. External entry ABBA seconds were
32.14 / 35.29 / 31.63 / 31.85. Fewer temporary lists did not establish speedup.
The runtime therefore retains its original complete revision-map comparisons.

**Prepared receiver scope.** This separate experiment reuses one private completed
scope instead of consing it on each guard invocation. The source/origin list,
instantiation calls, revision checks, callback protection and inverse checks remain.
The candidate binary SHA-256 is `96f4f232…75a8c`; the reference is
`e9a1a3d9…ff9e1`. New-minus-old medians below are us per operation, with 12 matched
cross-version samples. CPU-component medians need not add to a wall median.

| Phase / regime | Wall | Non-GC CPU | GC CPU | Wall residual | GC wall |
| --- | ---: | ---: | ---: | ---: | ---: |
| Trie retry / natural | -53.51 | -56.50 | -6.15 | -0.10 | -5.07 |
| Trie retry / collected | -0.45 | -21.10 | +11.30 | +2.60 | +12.79 |
| Trie retry / post-GC batch | +9.41 | +2.30 | +6.60 | +3.00 | +6.54 |
| Trie workflow / natural | +6.06 | -1.25 | +7.55 | +0.41 | +8.12 |
| RationalDict retry / natural | -52.00 | -33.10 | -11.30 | -2.95 | -11.35 |

Trie natural retry cross-version range is [-914.72, +48.88] us. This run does not
repeat the earlier +2157.40 us regression, but cannot establish a future tail bound.
Its same-version A/A median/range is -25.89 / [-857.23, +97.18] us; B/B is
-74.15 / [-204.49, -1.69] us. Drift remains large relative to the median benefit.
Charging forced GC **plus first call plus batch**, divided by all 11 calls,
Trie retry remains +20.96 us, range [-61.47, +359.93], including non-GC +9.77 us.
Other inclusive medians are RationalDict workflow/retry -39.87/-12.65 us and Trie
workflow -27.96 us. These adverse controls remain in the receipt; the library does
not inspect benchmark regime or change its production GC policy.

External entry wall ABBA seconds are 32.84 / 31.31 / 30.37 / 30.54. The first old
startup alone is 1.1044 s, versus approximately 0.015 s for the other runs, so an
unqualified external-entry speedup would conflate startup history with execution.
Loaded-entry wall is 31.693 / 31.289 / 30.346 / 30.511 s. Balanced means change by
-0.285 s wall, -0.255 s CPU, -0.293 s non-GC CPU, +0.038 s GC CPU and -0.030 s
residual. Old A/A wall changes -1.182 s and new B/B -0.943 s: **stable full-entry
speedup is not established**. Measured loaded-entry components (old/new means) are
setup 3.554/3.400 s, fixed prefix 4.470/4.434 s, batches 21.766/21.669 s and charged
forced-GC/first calls 0.448/0.423 s. Remaining time includes diagnostics, reporting,
statistics and collected-regime GC outside batch intervals; it is not all GC or
all scheduler delay. These are sums of disjoint measured intervals, not medians.

The original +2157.40 us retry observation remains evidence: CPU -66.60 us,
non-GC -136.00 us, GC CPU +69.40 us and wall residual about +2224.00 us, with two
collections on each side. It does not identify a Scheme algorithmic slowdown or
a specific external cause. Lean's signed-residual bound explicitly requires any
residual growth to fit inside measured CPU savings; no OS/GC latency bound is proved.
The receiver-scope law retains the receiver and every origin. The reference paired
revision law and malformed/length controls remain semantic audit evidence for the
withdrawn comparison, not claims about its adoption or allocation behavior.
Final Scheme acceptance: 128 modules / 1,266 cases in one process, exit 0 under
existing limits. All study phases, failures, retry/undo and Function oracles remain.

## Persistent output admission after GC

The derived table protocol now reuses the same explicit persistent-shape law and
weak-key admission helper as ordered tables. Only a successfully returned typed
`.acons`/`.remove` result is recorded as an admitted output. Initial/foreign roots
still require admission. If the backend has no ordered capability or does not
explicitly declare `.shape-preserving? #t`, ordinary shape admission still runs.
Carrier shape, child membership, both inverse comparisons, complete metadata
revision guards and original backend errors remain. No runtime GC-policy selector,
strong global root cache or new namespace is introduced.
The law assumes immutable persistent roots and a truthful backend declaration;
it does not certify arbitrary host mutation or arbitrary backend implementations.

The regression runs both declaration policies over a 64-binding represented Trie,
forces actual GC with live roots, exercises failed installation, restaging/retry,
undo and foreign-root rejection. Shape traversal counters are 1,035/276; this is
attribution only. Existing complex Function-bearing full workflows remain in the
study. Lean transfers the existing admitted-update theorem through an explicit
carrier isomorphism, preserving initial refusal, update errors/order and opaque
callback identity. This reuses TableOrder's existing closure law; it is not a
proof about GC scheduling, allocation, compiler behavior or wall-clock bounds.

### Preliminary paired receipt: first call, batch and tails

Reference linked head: `0525c02`, SHA-256 `96f4f232…75a8c`; candidate binary:
`5a34ea35…b2bd3`. Both execute the same expanded 31-phase workload: all earlier
28 phases plus three declared-policy controls (cold/workflow/retry). Every process
passes all 219 summaries with 64 bindings, 10 batch operations, six AB/BA and four
A/A plus four B/B pairs. ABBA uses four separate old/new/new/old processes, with
unchanged 1 GiB / 300 s limits and no overlapping local builds. Raw observations,
first-call/forced-GC histories and binaries stay outside Git.

Before this final set, a 28-phase exploratory set showed an inclusive median
+638.12 us and worst +9999.93 us; candidate B/B also had millisecond outliers.
It was not accepted as a speedup. Its run-0 stdout was accidentally overwritten
before backup; generated reports and the other three full transcripts survive.
It is incomplete diagnostic evidence, not the final acceptance set. All four
final 31-phase raw logs were saved to fresh paths with overwrite refusal.

For the original Trie retry workflow, cross-version post-GC inclusive cost charges
forced GC plus first call plus all ten batch calls, divided by 11. All **12/12**
matched observations improve: mean -345.26 us, median -355.92 us, empirical p90
-287.36 us, range [-418.10, -272.08] us. Disjoint mean contributions are:

| Charged component | Wall us | Non-GC CPU us | GC CPU us | Residual us |
| --- | ---: | ---: | ---: | ---: |
| Forced collection | +2.39 | +0.08 | +2.14 | +0.17 |
| First call | -31.61 | -31.32 | 0.00 | -0.30 |
| Ten-call batch | -316.03 | -320.93 | +2.52 | +2.38 |

Thus the saving is measured non-GC work in both first and later calls, not a forced
GC saving. The previous experiment's inclusive median +20.96 us is retained in
its receipt; it is not silently replaced by a favorable first-call-only result.
Natural/collected retry medians are -332.36/-310.61 us, but their adverse maxima
remain +28.97/+204.32 us. Timing improvement is not universal across samples.

The added same-process control compares two complete derived protocols differing
only in the existing declaration. Candidate post-GC inclusive observations again
win **12/12**: mean -379.95 us, median -335.87 us, p90 -290.20 us, range
[-845.39, -254.52] us. Each actual execution-order stratum wins 6/6, with worst
-254.52/-290.20 us. Weighted mean components are batch -351.53 us, first -26.31 us
and forced GC -2.12 us. Candidate same-policy B/B maxima are +25.81/+59.43 us;
reference A/A also retains a +405.01 us sample. No such adverse control is removed.

Old-binary negative controls do not establish a benefit from the declaration:
7 wins/5 losses, median -58.35 us, p90 +369.66 us and range
[-4431.18, +463.36] us. Their large favorable residuals make the mean misleading.
All reported quantiles are empirical small-sample diagnostics, not future tails.

Complete external entry ABBA wall seconds are 46.27 / 41.27 / 39.12 / 39.96.
These are the same **219-summary workload**, not compared against earlier smaller
studies. Startup wall is 1.046/0.074/0.039/0.104 s. Loaded-entry wall is
45.178/41.178/39.071/39.842 s: balanced mean improves 2.386 s, comprising CPU
-1.667 s (non-GC -1.504, GC -0.164) and residual -0.718 s. But old A/A drifts
-5.336 s and new B/B -2.107 s. **Stable full-entry wall speedup and a latency
bound remain unproved**, despite the paired complete-retry evidence above.
The measured entry includes setup, prefixes, reporting and all controls.

Final local Scheme acceptance: 128 modules / 1,267 cases, one process, normal exit
0 with existing limits. Complete conversion, equality, retry, inverse and Function
oracles remain. Only this compact receipt is versioned; raw data is not committed.

Observed execution retains ordinary admission for a fresh point-update output,
including the actual validator getter's access refusal. Only unobserved calls may
promote the declared persistent output. The existing observed-denial theorem and
an exact-cause regression cover this read-authority boundary; previously admitted
roots keep the original weak-cache semantics. The preliminary receipt above used
the pre-observation-guard binary and is superseded by the final receipt below.

### Final receipt with observed-validator protection

This receipt uses the final guarded implementation, binary SHA-256
`2626be4b…d785c`, against the same `0525c02` reference (`96f4f232…75a8c`).
All four fresh-path ABBA logs complete 219 summaries, 64 bindings, ten batch
operations and six AB/BA plus four A/A and four B/B controls. Every original phase
remains. No builds overlap measurements; 1 GiB / 300 s limits are unchanged.
The complete single-process suite passes 128 modules / 1,267 cases, including
exact validator-access denial and both declaration policies across real GC.
Shape-work counters with the additional observed controls are 1,065/306; they
are not the performance acceptance criterion.

For the original full Trie retry, inclusive post-GC new-minus-old observations
charge forced collection + first call + ten batch calls, divided by 11:
**12 wins / 0 losses**, mean -387.59 us, median -378.98 us, empirical p90
-237.83 us, range [-776.57, -206.38] us. Every adverse sample is retained.
The additive mean components are:

| Charged component | Wall us | Non-GC CPU us | GC CPU us | Residual us |
| --- | ---: | ---: | ---: | ---: |
| Forced collection | -3.87 | -0.07 | -3.69 | -0.11 |
| First call | -55.07 | -53.53 | 0.00 | -1.54 |
| Ten-call batch | -328.66 | -334.10 | +3.92 | +1.52 |

GC savings do not explain the improvement: mean GC CPU across these components
is approximately +0.23 us. First and later calls both reduce non-GC work.
Natural retry still has an adverse +733.59 us sample despite its -331.40 us
median. Collected retry improves in all 12 samples, range [-438.31, -257.83] us.
Post-GC batch A/A and B/B ranges remain [-133.71, +24.63] and
[-180.60, +20.19] us respectively; noise is not discarded.

The same-process two-derived-protocol declaration control also wins 12/12:
mean -335.29 us, median -343.99 us, p90 -263.71 us, range
[-429.35, -262.09] us. Each actual order stratum wins 6/6, with worst
-274.44/-262.09 us. Candidate same-policy B/B maxima are +41.46/+31.17 us;
reference A/A maxima are +39.23/+30.11 us. The old-binary negative control has
5 wins/7 losses, median +11.12 us, p90 +225.46 us and range
[-592.67, +237.49] us. These are finite observations, not distributional bounds.

Complete external entry ABBA wall seconds are 37.60 / 36.25 / 35.42 / 36.24;
startup wall is 1.129/0.014/0.015/0.040 s. Loaded-entry wall is
36.454/36.225/35.393/36.192 s. Both cross-version directions improve, by
0.229/0.799 s. Balanced loaded mean improves 0.514 s: CPU -0.608 s,
non-GC -0.702 s, GC CPU **+0.094 s**, residual **+0.094 s**. Measured setup mean
actually grows 0.016 s, while batch wall falls 0.483 s. The result is not credited
to repeated metadata preparation or to lower GC time. Old A/A changes -0.262 s
and new B/B -0.832 s; stable full-entry speedup and tail guarantees remain unproved.
The startup-sensitive external mean improvement must not be substituted for the
loaded-entry comparison. Lean proves conditional shape/admission semantics and
observed refusal preservation, not timing of this host or its collector.

### Whole-entry preparation candidate: withdrawn after tail acceptance

The earlier candidate B/B difference of -0.832335 s decomposes into
-0.514042 s non-GC CPU, -0.333111 s GC CPU and +0.014818 s signed wall-minus-CPU
residual. It is same-version drift, not evidence of an 0.832 s selector/GC defect.
Preparation, fixed prefixes, forced collection, first call and batches remain
separately charged. Unattributed entry work includes reporting and collected-mode
GC outside the explicit post-GC intervals; residual is not automatically scheduler
wait, and summing stage medians is invalid.

A concrete candidate removed eager source/derived fixture construction from cold,
prepare and equality slices, while retaining every timed action and oracle. The
same compiled workload supplied eager/selected controls; no library policy, GC
mode, count, timeout or resource bound changed. Eight complete width-64, batch-10,
6-pair processes ran eager/selected/selected/eager/selected/eager/eager/selected,
without overlapping local builds. Every process returned 0 with 219 summaries.
This study preceded the declaration-preparation correction below: its executable
SHA-256 was `2626be4bb8918b55a66d57786721bb65b526bf6fe1c7ab51ebf3be04f80d785c`,
compiled workload SCM SHA-256
`4d2fd0e194bb0e9dace0b6a28c34abecdb2afbabf29b63fbcc2d778179eecc0a`.
It is not a measurement of the subsequent final library binary.

| Matched process slots (eager → selected) | External wall, s | Loaded entry delta, s | Non-GC CPU delta, s | GC CPU delta, s | Residual delta, s |
| --- | --- | --- | --- | --- | --- |
| 0 → 1 | 37.79 → 36.53 | -1.296 | -0.903 | -0.085 | -0.309 |
| 3 → 2 | 35.16 → 36.78 | +1.614 | +0.722 | +0.233 | +0.660 |
| 5 → 4 | 36.92 → 35.75 | -1.161 | -0.525 | -0.065 | -0.571 |
| 6 → 7 | 37.05 → 36.14 | -0.907 | -0.542 | -0.061 | -0.304 |

The loaded-entry mean delta is -437.376 ms, with 3 wins/1 loss and empirical
p90/max **+1.614399 s** (four paired process observations, not a population bound).
Preparation CPU falls in all four pairs by 77–352 ms. Its wall delta ranges
-360 to +93 ms; the adverse pair includes +171 ms preparation residual.
First-post-GC call CPU deltas range -6.837 to +7.788 ms over the whole entry;
first-call wall deltas range -24.021 to +62.027 ms. Startup wall was 14–40 ms,
reported separately and still included in external wall. Eager A/A differences
are -2.631/+0.131 s; selected B/B differences are +0.280/+0.385 s. Neither control
is silently removed or declared to prove bounded variance.

Crucially, the actual Trie cold-call wall tails fail acceptance. Each regime has
24 matched candidate-side calls, preserving every round: natural has 22 losses,
mean +84.026 us, empirical p90 +252.509 us, max +326.204 us; collected has 21 losses,
mean +144.545 us, p90 +393.105 us, max +522.065 us. Natural retry also retains
9 losses/15 wins and max +180.507 us. These within-process fixture observations
are not 24 independent process samples. Changed preparation demonstrably changes
subsequent histories; fewer setup operations cannot establish a safe whole-workflow
speedup. **The pruning candidate was withdrawn, including its temporary CLI switch.**
The default fixture preparation and every check remain unchanged. Setup work counts
are now printed separately, with their reporting charged to the complete entry.

Raw stdout, timing receipts and signed histories remain read-only outside Git in
`/tmp/poo-fixture-entry-20261023.dU1Upx/`. The bounded investigation is complete;
there is no stable entry/tail improvement claim and no promise to eliminate future
wall variation. `measuredEntry_prepare_bound` requires the saving to cover every
other cost and residual; `measuredTail_bound` requires every retained observation
to meet a bound. Lean examples explicitly refute admission based only on a lower
mean or preparation cost. These are conditional accounting laws, not VM/GC proofs.

### Ordered measurement reporting and complete-entry accounting

The paired driver now finishes both ordered samples before formatting or flushing
records. This removes reporter allocation/IO from the gap between A and B without
removing it from complete-entry wall time. AB/BA and A/A/B/B orders, setup, fixed
prefixes, natural/collected/post-GC regimes, forced collection, first calls, batches,
independent oracles and all 219 summaries remain. On a sample failure it reports
the successful prefix once, then preserves the original cause if reporting succeeds;
a reporter failure is itself fatal. Three regressions cover order, both refusal
positions and reporter failure. Lean's `measurePair_status`, `measurePair_complete`
and `measurePair_second_error` model finite ordered sampling and its exact error;
reporter noninterference/success and faithful sample interpretation are premises,
not proofs of Scheme IO, GC or VM timing.

Standard library, test-program and benchmark-module preparation all use Gambit's
`time` form. Parent preparation CPU/GC, enclosing command wall, binary startup,
loaded-entry CPU/GC, setup/prefix/first/batch/forced costs and signed residuals stay
separate. Parent CPU is not the whole launcher/child envelope. No warm cache allows
skipping the standard dependency check. Profiling the released expander import
hook found shared source imports (many already cached), not evidence that the same
module was repeatedly expanded. A paired-list `andmap` candidate lost 16/16 focused
comparisons; a cached-vector fold lost 15/16 and allocated more. Neither is shipped.

A fresh source snapshot of Scheme commit `80a788a` was built by the standard package
builder and passed all 128 modules/1270 cases. The reporter candidate passed all
128 modules/1273 cases. Both used the same preparation instrumentation and release.
Eight complete entries ran reference/candidate/candidate/reference/candidate/
reference/reference/candidate, width 64, ten calls and six rounds, without overlapping
local builds. Every entry exited 0 and produced 219 summaries. Raw stdout and timings
are read-only outside Git at `/tmp/poo-report-pairs-20261023.OTYvyh/`.

| Matched process slots | External wall reference → candidate, s | Loaded non-GC CPU delta, s | Loaded GC CPU delta, s | Loaded residual delta, s |
| --- | ---: | ---: | ---: | ---: |
| 0 → 1 | 51.68 → 52.54 | -0.132 | -0.059 | -0.087 |
| 3 → 2 | 49.00 → 48.01 | -0.475 | -0.173 | -0.285 |
| 5 → 4 | 52.93 → 50.12 | -0.749 | -0.343 | -0.828 |
| 6 → 7 | 55.85 → 67.59 | +2.752 | +0.281 | +9.468 |

External paired mean is **+2.20 s**, with 2 wins/2 losses and empirical p90/max
**+11.74 s**; four process pairs are not a distributional tail bound. The adverse
pair's library-parent wall differs by only +0.116 s. Thus neither lower GC nor
less dependency preparation explains the whole tail. First-process startup wall
was 1.296 s (reference) and 2.652 s (candidate), with CPU about 0.032 s each; later
starts are retained too. These are neither timed outliers to delete nor a stable
speedup claim. Same-version controls and exact keyed workflow tails remain in the
raw study. A finite observation does not establish a cause for wall-minus-CPU.

Source and implementation identity: reference/candidate `closure-measure.ss`
SHA-256 are `fd1a21528f988d45cd12160104ca474b3f8a45b1716186540b14ba4f19c9aba9` /
`0e1f48da22e33ab323f3028b0b69bb30b3c5643e5a581f42befbf724dbe7c47d`;
workload-source hashes are `a2c53fd98ff8fbf3744f333bc22fa9518e0409633ca5d834f70d823153c1c94c` /
`f6db05ae6acecac39418a2d551affe75fff61db691ee3f5be4826772530b9f69`.
Executable hashes are `3db240c5156458ae16aa0aad9bdb6551c4fa2a1c4126ad3e580d0e2f5b0fa4a4` /
`68a60c8a84d9563ea7fdd40d00baa7dd197fcdcdf7b1a0d7c79d1025a4042719`.
Generated `~0.scm` implementation hashes are
`68b21ce92d7f3fbb09f7a795c20336d57d79237643a9c002c3abff8316fa5b28` /
`99983e2c656de85d2b259d09dedd3ba8383d09e67e2e420343effa52938d0983`.
The loader SCM alone cannot identify a changed compiled implementation.

#### Standard minimum-heap policy: complete wall gain, workflow tail refusal

A second study used the SAME candidate executable/source in all eight entries,
default/minimum/minimum/default/minimum/default/default/minimum. The only policy
difference was Gambit's documented `min-heap=32M`, within the unchanged 1 GiB
maximum; all stage deadlines, checks, GC regimes and preparation remained. Every
entry passed 219 summaries. This is a hot-artifact dependency-check/full-execution
study, not a new cold compilation speed claim. Raw signed histories, output and
outer timings are at `/tmp/poo-heap-pairs-20261023.8rBkpa/`; the measured source and
binary hashes are the candidate hashes above, before the later declaration fix.

| Pair | External wall default → minimum, s | Loaded non-GC CPU delta, s | Loaded GC CPU delta, s | Loaded residual delta, s |
| --- | ---: | ---: | ---: | ---: |
| 0 → 1 | 114.51 → 87.81 | +0.462 | -3.845 | -14.455 |
| 3 → 2 | 115.35 → 81.59 | -3.987 | -4.526 | -10.253 |
| 5 → 4 | 111.37 → 95.83 | -0.957 | -3.945 | -21.568 |
| 6 → 7 | 78.52 → 61.15 | -1.415 | -3.511 | -6.939 |

All four external pairs win: mean -23.3425 s, empirical p90/max -15.54 s, range
[-33.76, -15.54] s. Group maxima are 115.35/95.83 s. Nevertheless same-policy
A/A changes +0.84/-32.85 s and B/B -6.22/-34.68 s; the host's large wall variation
is retained, not credited to the policy. Loaded means split into -1.4745 s non-GC
CPU, -3.9569 s GC CPU and -13.3039 s residual. Parent preparation wall savings
range **-13.940 to +10.509 s**, mean -4.147 s; repeated preparation itself is not
uniformly faster. Startup wall is 0.045–0.171 s for default and 0.015–0.122 s for
minimum, with every first process retained. One shell-stage receipt says
`real 2.:0`; its command-envelope residual is unavailable, not repaired. Internal
parent statistics and outer complete wall remain valid for that process.

**The policy is not made the default.** Retaining every keyed per-workflow sample
exposes adverse tails despite the complete-entry gain:

| Workflow / charged regime | Wins/losses (24 matched calls) | Mean delta, us | Empirical p90, us | Maximum, us |
| --- | ---: | ---: | ---: | ---: |
| Trie complete / collected | 9 / 15 | +1034.19 | +4009.70 | +7488.11 |
| Trie retry / post-GC batch | 11 / 13 | -30.78 | +2203.70 | +3000.09 |
| Trie retry / forced GC + first + batch | 11 / 13 | +57.55 | +2729.33 | +2787.29 |
| Rational complete / natural | 16 / 8 | +272.64 | +1805.11 | +10064.60 |

The inclusive row charges forced collection, the first call and ten batch calls,
divided by 11, before computing tails. Its two actual order strata retain 5/7 and
6/6 wins/losses with adverse maxima +2729.33/+2787.29 us. Same-policy inclusive
retry tails also vary (A/A max +501.07/+1969.23 us, B/B +1519.25/+3574.54 us);
those controls do not justify deleting cross-policy losses. These are 24 keyed
calls from four process pairs, not 24 independent process observations. Lower GC
CPU, a lower average or a lower whole-entry maximum alone does not close every
workflow's acceptance. No stable future tail guarantee is claimed. The bounded
policy investigation ends with the existing default preserved; no environment
variable, scheduler, collector, reduced check count or enlarged limit is added.
`measuredEntry_gc_bound` states the conditional complete-cost criterion, including
preparation and residual, rather than proving the installed collector's behavior.

### Complete translation-declaration preparation

The next TODO unit closes a reproducible shared preparation omission, rather than
adding another performance scenario. Before the correction, all three public
constructors (`table-isomorphism`, derived fold `.isomorphism`, `table-wrapper`)
accepted a later computed value Domain getter rewriting an earlier key Domain;
the returned declaration then retained incompatible current endpoints. Sampling
revision stamps only after that rewrite did not detect it.

The shared continuation now protects parents/converters during source discovery,
then protects the complete child/origin scope during endpoint admission and
callback selection. Existing object mutation guards, source closure, `using` and
FUN/IO supply the protocol. An explicit lexical boundary keeps incompatible
endpoint refusal ahead of callback getters. There is no alternate type relation,
new namespace or second transport/fold implementation.

Twelve independent constructor/victim combinations cover converter, source,
target and child metadata, unchanged revisions on refusal, exact getter causes,
fresh retry and type-before-callback failure order. `prepare-ledger-transport`
uses existing Reader bind: reprepare once per request, transport its original
base/delta, install privately and consume only on success. Its service example
retains the exact checked Function through construction refusal, conflict,
rediscovery/retry and inverse recovery. Lean's `translationPreparation_compatible`
reuses `indexPreparation_frame` to preserve all four exact endpoint pairs across
protected edits. Faithful metadata/source snapshots and supported sequential
writes are premises; arbitrary raw mutation, callback termination, physical GC
and Scheme compiler correctness are outside this finite future-work unit.

### Closed target construction and atomic transfer

A `.key-table` capability preserves the backend's key equality for private owner
and edit registries, independently of business-row representation and indexes.
Closed index/order/representation constructors retain that capability as well as
complete construction and atomic delta installation. Fold bridges now compose
these whole operations; they do not expand a valid index swap into point writes.
See [table-fold.md](table-fold.md) for the contract, failure order and finite laws.

The shared construction guard now has an explicit finite `Except` model in
`TableRepresentation.lean`: preparation precedes revision observation; stale
families refuse with the supplied cause; current families preserve the exact
operation outcome. The encountered carrier kernel separately proves admission
failure, left-inverse refusal and stable roundtrip identity. Scheme regressions
observe actual callback order, exact thrown causes and recovery after refusal.
These equations do not prove arbitrary callback termination or dynamic control,
and code-generation size is not a proof of compiler or wall-clock performance.
