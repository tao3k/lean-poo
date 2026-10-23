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
