# Property diagnostics and test integration

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Source-consistent error classification and terminal diagnostics](#source-consistent-error-classification-and-terminal-diagnostics)
- [Diagnostic request admission before typed preparation](#diagnostic-request-admission-before-typed-preparation)
- [Prepared named diagnostics across report observation](#prepared-named-diagnostics-across-report-observation)
- [Captured preparation refusals across diagnostic rendering](#captured-preparation-refusals-across-diagnostic-rendering)

## Source-consistent error classification and terminal diagnostics

Audit reproduced a completed `unsupported` report whose `report-current?` was
already false: the original draw threw, the error classifier revised its own
specification source, and `failure-status` checked currentness only before calling
that classifier. Inspection used the same exit. A classifier could also start a
nested generator after retiring the current run and execute its mapper before
publication was eventually checked.

`failure-status` now reuses the existing hygienic `with-current` action. A local
refusal continuation returns `stale`; the standard dynamic checker also protects
nested generator/domain callbacks. Normal return observes the same currentness
again. No new report, exception type, wrapper per callback or classification engine
is added. Run-local scopes unwind normally and are not stored on reports.

The original callback cause always remains the report's cause. A secondary
classifier or source-observer exception yields `error` with that original cause;
a classifier's normal return after source revision yields `stale`. Precise stale
and built-in bounded-generation exhaustion keep their precedence and do not invoke
the application classifier. Stable lawful classifications remain `error`,
`exhausted` or `unsupported` (and the existing allowed `stale` outcome). Invalid
classification symbols remain API errors; they are not accepted as reports.
Interrupted shrinking retains the last confirmed witness, charged attempts and
accepted steps, but cannot certify a minimum or authorize concrete replay.

Six generic regression cases in `examples/property-scopes.ss` cover execution and
inspection, nested effect suppression/unwinding, secondary errors, built-in outcome
precedence, partial shrink progress and explicit seed replay. They register in the
existing independent standard TestSuite; the isolated stdlib-only library grows
from 97 to 103 cases. There is no new module inventory or test runner.

`service-classification-action` in `examples/generated-products.ss` provides the
complete downstream composition. POO owns a strict service Record with UInt count
and checked Function, typed sampler sources and validation. The independent runner
owns the application error classifier and generic report. Reader/FUN bind delivers
that report once. Negotiation replaces a declared recipe while classifying its
service failure; the obsolete normal classification is refused, the original
cause is retained and old seed replay is rejected. Explicit fresh preparation
then draws validated Records, shrinks the service discrepancy, retains Function
argument checks and supports both concrete and seed replay. Reusing the old action
still refuses without another classification. PropertyConfiguration is unchanged.

Six `classifyFailure` laws in `PropertyScopes.lean` reuse `guardedGeneration` and
the existing CheckStatus vocabulary. They establish stale preflight, revision
refusal, secondary-error handling, exact stable classification, preservation of
the original cause and non-passing/non-falsified outcomes under a lawful classifier.
Top-level examples exercise recipe replacement and explicit fresh epochs. Accurate
pure total source predicates, faithful host dynamic scope, terminating serial
callbacks and valid classification outputs are premises. Observer exceptions and
host continuation cleanup remain executable tests; no Scheme evaluator, arbitrary
callback termination, GC or wall-clock behavior is proved.

The pinned [Rackcheck property executor](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/prop.rkt)
separates property execution and shrink-tree descent but intentionally maps property
exceptions through `pass?` to falsification while retaining the exception. This RFC
keeps its established stricter failure vocabulary; dynamic source authority is our
extension, not a missing Rackcheck promise. Lazy tree structure, forcing policy,
random schedule, domains, quotas, independent library ownership and process/heap
limits are unchanged. Classification source checks have a cost; no wall-clock
speedup is inferred from suppressed callbacks.


## Diagnostic request admission before typed preparation

The audit reproduced a diagnostic ordering defect through the public typed
inspect-generator entry: count -1 still forced a computed generation getter. Its
exception replaced the configuration refusal, with one metadata evaluation and no
legitimate inspection. Static diagnostic requests must be admitted before source
observation, descriptor discovery, owned factories or raw binding.

The existing generic configuration conjunction now has one exported module owner,
check-inspection-request. Both generic inspection and the typed bridge call it;
there is no new request record, wrapper stack, namespace, scheduler or observer
registry. It recognizes exact nonnegative seed/count/size/depth/proposal-budget
values and callable label/classifier hooks without invoking them. The same ordinary
Error and message remain the request failure. Zero count and zero traversal fuel
are legal; arbitrary-size exact seeds remain legal. This preserves the deliberate
difference from Rackcheck's pinned gen/core.rkt contract-out, whose sample count
is positive: we follow its contract-before-execution separation, not its API or
random schedule. PBT remains future work beyond the author's concrete constructs.

Five regression cases cover every numeric control with negative, fractional,
inexact and wrong-type values; malformed callbacks in both layers; zero controls
with no draws/labels; exact false/object preparation causes and stale sources; and
a complete callback-service workflow. The latter inspects bounded FunctionArguments
with optional/keyword parameters and nested List/Function callbacks, compares
wrapped calls, then runs FUN-delivered failure shrinking and seeded/concrete replay.
Owner revision invalidates the old diagnostic and witness; a fresh corrected
service passes. Static rejection performs no metadata or source callbacks, while
valid preparation errors remain ordinary exceptions and execution retains existing
inspection status, budget and cause behavior. This adds no property evaluation to
the diagnostic engine: the example explicitly supplies a label callback.

Ten Lean laws normalize exact integers into optional Int controls, establish
nonnegative/malformed/callable admission and legal zero budgets, and compose the
existing admitReplayRequest and guardedGeneration boundaries. Invalid requests skip
all preparation, valid requests keep the original guarded result, stale/revised
sources refuse, and original causes and stable results remain exact. Top-level
examples include a large exact seed and stale authority behind an invalid request.
Faithful host normalization, callable recognition, source accuracy, callback
termination and standard FUN/IO delivery remain premises; this is not a proof of
Gerbil expansion/runtime, elapsed cost or arbitrary effect rollback. All complete
checks and process resource limits remain unchanged. No latency claim is made.

## Prepared named diagnostics across report observation

The audit reproduced a presentation ownership defect: report-diagnostics admitted
caller-owned binding names, then report-current? could invoke a source observer
which rewrote those names. A request for `declared` consequently rendered
`retargeted`. The typed facade also read computed `execution` metadata before
admitting the binding directory; preparation-only reports ignored invalid names.

The existing generic property module now owns prepare-report-diagnostics. It
admits a finite, unique symbolic directory and copies its spine once, returning
an ordinary reusable formatter. report-diagnostics delegates to it; the typed
facade prepares it before reading computed report metadata and passes a completed
execution directly to the same formatter. Standard :std/test consumers can bind
this formatter once and reuse it without a POO dependency. This follows the
existing higher-order FUN style; there is no new namespace, report record, source
cache, authority protocol or additional value wrapper. Generated payloads remain
shared. Empty or width-mismatched rows remain ordinary data, never truncated zip
bindings. A prepared formatter captures names, not report status or currentness.

Four independent regressions cover cyclic caller edits during observation,
reusable vector/false binding, stale standard assertions, malformed/duplicate
requests before observers, exact historical causes and unmatched rows. Independent
acceptance increases from 196 to 200 cases. Two typed service cases reject invalid
names before computed report reads and combine inherited getters, FunctionArguments,
nested List/Function service calls, Record PropertyConfiguration, FUN delivery,
failure shrinking and both replay forms. No callback exception becomes a false
property, no stale report becomes passing, and historical failures remain readable.

Eight finite Lean laws model full-row binding and capture-before-observe: invalid
names skip observation, old names survive state revision, original causes and
false currentness remain exact, empty/mismatched rows remain undecorated and fresh
invocations capture fresh names. Executable examples include a false payload,
duplicate rejection and an observer replacing the caller directory. Faithful
finite host copying, symbol recognition, observer accuracy, callback termination
and existing FUN/IO/standard-test delivery remain premises. This advances the
paper's future work, not compiler/runtime verification. All complete checks,
compiler guards and process resource limits remain unchanged; no timing claim.

A downstream suite can prepare its renderer before any assertion observations:

```scheme
(import :std/test
        (prefix-in :clan/poo/testing/property p.)
        (prefix-in :clan/poo/testing/property/test property.))
(def render-request (p.prepare-report-diagnostics '(request)))
;; Inside an ordinary test-case, report is the existing completed kernel report.
;; (property.check-property report diagnostics: render-request)
```

The formatter does not run a generator or authorize a passed assertion. Reuse
with another report always observes that report's own authority.

## Captured preparation refusals across diagnostic rendering

The audit reproduced a break in [authoritative standard assertions and checked diagnostic rendering](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/diagnostics.md#authoritative-standard-assertions-and-checked-diagnostic-rendering)'s original-cause guarantee. With no kernel
execution, `require-passed` admitted a finite symbolic `refusal:` alist and retained
its caller-owned directory. A formatter could replace one field with a symbol and
then raise a secondary cause. Fallback traversal subsequently raised a host
RuntimeException rather than the standard TestError carrying the preparation
cause and the separate rendering fault. This is a library-owned presentation
boundary, not a request to sandbox arbitrary Scheme effects.

The existing assertion owner now captures the fallback directory AND each field
pair with one ordinary map before invoking the formatter. Header selection uses
that same captured receipt; there is no new record, wrapper, runner, namespace or
second renderer. Copies are shallow: payload identities, including false causes,
Function values and mutable domain objects, remain shared under their declared
ownership laws. The boundary admits a finite symbolic alist before copying it;
malformed/cyclic initial requests still refuse before any formatter callback.

Only fallback ownership changes. A present current passed report still follows
its original source checks and error behavior. Missing execution never passes;
canonical status/cause cannot be replaced by display fields. A valid formatter's
returned display fields still take precedence over fallback details. A malformed
return or thrown rendering cause keeps the original refusal, and the secondary
fault remains `diagnostic-cause`. No property, generation, shrinking or replay is
repeated for diagnostic delivery. User effects and nested mutable payload writes
are not rolled back or deep-copied.

Three generic regression cases exercise field-pair edits, improper/cyclic spine
edits, exact primary and secondary identities, payload identity, malformed alias
returns, valid replacement display fields and pre-callback request rejection.
The isolated standard-library package requires 227 cases; all previous cases stay.
A complex existing Record/Map/Function service uses a FUN-produced preparation
refusal, corrupts its supplied presentation fields and throws while rendering,
and verifies the standard TestError still retains the preparation phase and both
causes. Correct configuration starts a fresh run, really shrinks the service
state, preserves nested Function contracts and both replay paths, rejects an old
source epoch, and admits an explicitly freshly prepared retry.

Six finite laws extend the existing PropertyScopes model: initial-field retention,
exact rendering result/cause, unchanged fields after state changes, renderer
noninterference and composition with the existing missing-execution assertion
rule. Three top-level examples retain field order, duplicate display names, false
data and false causes. Faithful host shallow allocation, finite admitted fields,
source-observer laws, terminating sequential callbacks and standard TestError
transport are premises. These laws do not prove host mutation/exception machinery,
arbitrary concurrent writes, or immutability of shared payloads. This advances
the paper's future work.

The Rackcheck/Quickcheck comparison retains the existing generator/tree algebra;
this unit closes our [authoritative standard assertions and checked diagnostic rendering](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/diagnostics.md#authoritative-standard-assertions-and-checked-diagnostic-rendering) standard-test ownership guarantee rather than claiming a
missing Racket feature or changing its shrinking policy. Gerbil's existing module,
map, error class and :std/test boundary own delivery. Design review deliberately
kept capture at the one assertion boundary rather than adding copy/validation
wrappers to typed reports or FUN consumers. Complete checks, original heaps,
natural compiler/test completion and cancellation behavior remain unchanged.
No latency or universal allocation improvement is claimed.

