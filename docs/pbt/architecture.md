# Architecture and source comparison

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Earlier acceptance summary](#earlier-acceptance-summary)
- [Module ownership and independent-library boundary](#module-ownership-and-independent-library-boundary)
- [Quickcheck and Rackcheck source comparison](#quickcheck-and-rackcheck-source-comparison)
- [Decision](#decision)
- [Source basis and existing capabilities](#source-basis-and-existing-capabilities)
- [Scope and explicit boundaries](#scope-and-explicit-boundaries)
- [Abstraction and implementation review](#abstraction-and-implementation-review)

- [Release readiness and abstraction review](#release-readiness-and-abstraction-review)

## Earlier acceptance summary

Current finite acceptance includes the finite protocol features. The companion Gerbil RFC owns the
current developer interface; [property-kernel.md](../property-kernel.md) maps its
standard test/debug integration, bounded diagnostics and configuration guards to
Lean laws. [inherited declaration scope for typed differential fixtures](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/model-traces.md#inherited-declaration-scope-for-typed-differential-fixtures) extends inherited typed-fixture declaration scope; [first-observation typed trace declaration preparation](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/model-traces.md#first-observation-typed-trace-declaration-preparation) unifies
first-observation typed trace preparation and preserves earlier epochs across
computed fields and Record normalization. PropertyScopes supplies finite serial
observer laws, not arbitrary callback/evaluator or concurrency verification.
[finite fixed-product preparation and retained trees](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/data-generation.md#finite-fixed-product-preparation-and-retained-trees) extends fixed products with finite constructor admission and retained
drawing. PropertyProducts proves exact field order/length and continuation-seed
equivalence; the independent companion library now requires 115 cases. The
Scheme iterative candidate is not admitted after GC cost acceptance; the existing
bind/checkpoint draw remains the production strategy.
[authoritative standard assertions and checked diagnostic rendering](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/diagnostics.md#authoritative-standard-assertions-and-checked-diagnostic-rendering) separates actual report admission from arbitrary diagnostic rendering.
PropertyScopes adds seven finite presence/status/source laws; the independent
companion suite now requires 121 cases and eleven CLI refusals.
Historical audit identities below remain historical receipts.

[inherited authority for finite function observations](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/function-generation.md#inherited-authority-for-finite-function-observations) closes inherited authority on retained finite function observation. Seven
PropertyScopes laws reuse guardedGeneration and exact-row lookup for parent/owner
refusal, stable results, retirement, original errors and present/absent rows.
The companion's independent suite requires 127 cases, with contracted Record/FUN
retry, shrinking and portable replay. Runtime dynamic-scope fidelity, truthful
observers and finite serial terminating actions remain premises.

[portable vector copy preparation and shared resource credits](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/data-generation.md#portable-vector-copy-preparation-and-shared-resource-credits) closes portable vector copying before destination allocation/child inspection.
PropertyReplay adds eight finite credit/preparation laws in the existing namespace:
shared accounting, minimum width, necessary preflight, width/depth refusal, empty
admission and exact admitted results/errors. The standard companion copier uses
Gerbil's forward vector-fold/index; isolated acceptance requires 132 cases plus a
contracted Record/FUN corpus retry. Host readers, encoders, allocator bytes and GC
remain outside these logical-credit proofs; no wall-clock improvement is claimed.

[bounded exact-ratio generation and canonical shrinking](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/pbt/function-generation.md#bounded-exact-ratio-generation-and-canonical-shrinking) adds bounded exact-ratio Rational generation. PropertyNumbers reuses standard
Rat normalization with ten laws for canonical keys, pair refusal/recovery, bounds,
zero/integral profiles and strict value descent. Independent acceptance requires
139 cases; recursive typed carriers and a Record/List/Function FUN service exercise
shrinking, pair corpus replay, old-source refusal and corrected fresh preparation.
The Scheme Rational descriptor still includes finite inexact values, but default
drawing is exact. No Float/Real/Number fallback or IEEE coverage is asserted.
Host exact arithmetic/exactification, codec fidelity and random ranges are premises.

- Status: implemented; finite acceptance and evidence boundaries are recorded below.
- Date: 2026-10-27.
- Targets: Gerbil-POO PR #13 and Lean-POO PR #13.
- Implementation acceptance: reusable protocol, collection controls and downstream integration are implemented; CI is checked independently for each submitted revision.

## Module ownership and independent-library boundary

The generic library uses ordinary modules under `testing/property`, with direct
imports. The runner is `testing/property.ss`; generator, model, replay and test
support live in `testing/property/`. The root `defbuild-script` builds them with
all other package modules. There is no separate package or forwarding facade.

| Module | Responsibility | Dependencies |
| --- | --- | --- |
| `testing/property/generator.ss` | Invocation-local random sources, unit/map/bind/sequence, lazy value-and-shrink provenance | Gerbil standard library |
| `testing/property.ss` | Explicit domain specifications, finite checks, bounded child consumption, reports and both replay forms | Generic generator module and standard library |
| `testing/property/model.ss` | Pure model folds, dependency retirement, bounded trace draw, scoped first-difference comparison | Generic generator module and Gerbil standard library |
| `testing/type.ss` | Type-driven derivation, Record contracts, bounded membership, POO source observations, typed reports and Reader/FUN actions | POO and generic modules |
| `testing/function.ss` | FunctionArguments derivation from checked signatures | POO function/signature modules and testing/type |
| `testing/generation-graph.ss`, `testing/recursive-generation.ss` | Bounded descriptor graph compilation and safe recursive derivations | POO type/recursive constructions |

Top-level `property-testing.ss`, `function-testing.ss`, `generation-graph.ss` and
`recursive-generation.ss` are moved, with all importers/build inventories migrated.
There are no compatibility forwarding files. Existing `support/testing.ss` and
`t/table-testing.ss` keep their distinct support/test-only ownership.

The generic modules import no POO object, Type, Record, lens or revision APIs.
Their records are Gerbil structs; domain admission and cost are mandatory caller
callbacks. POO retains its Record declarations and supplies bounded typed
admission, normalization and source-current callbacks at the boundary. Generality
is parametric; it is not a fallback to an unconstrained POO `Any` descriptor.

The independent-library acceptance copies these five generic source modules and
`examples/property-kernel.ss` and its ordinary product/filter/scope/size/trace helpers
into a temporary standard Gerbil package, declares
`clan/poo/testing`, and compiles with `defbuild-script`. The compiled suite runs
through `gerbil test`. It requires all 87 case receipts, an error-free result and
correct process exit status under the existing heap and timeout limits. The
isolated installation has no object, MOP or typed testing modules. Sharing a
module path does not import parent modules. This demonstrates code dependency
independence; it is not an upstream publication.

## Quickcheck and Rackcheck source comparison

The source references are pinned independently of the local compiler:

- [Racket Quickcheck](https://github.com/ifigueroap/racket-quickcheck/tree/0b6902d8d79973ec959f99e56ccba038beca8fe9):
  `quickcheck/private/generator.rkt` combines return/bind/sequence and splits the
  random source; `quickcheck/generator.rkt` expands `bind-generators` into that
  algebra. Ordinary Racket generators do not require Typed Racket.
- [Rackcheck](https://github.com/Bogdanp/rackcheck/tree/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7):
  `rackcheck-lib/gen/core.rkt` maps and binds shrink trees, retaining a child random
  state for dependent regeneration; `gen/base.rkt` builds lazy list shrink trees.

We adopt composition of generated values AND their provenance. A non-injective
map retains its preimage tree without asking for an inverse. Bind first explores
parent shrinks, regenerating each dependent child with the same captured child
seed, then explores that child's own shrinks. Gerbil's standard `in-coroutine` /
Iterator protocol provides lazy children; no thread, custom stream framework or
process-global sample cache is introduced. Seed splitting follows the compositional
idea, not byte-for-byte random sequence compatibility with either Racket library.

A generic generator and its intermediate shrink nodes must honor its declared
semantic domain; a malformed selector/callback is an error, not a false property.
The final property specification explicitly admits values and supplies a natural
measure. POO-specific generation-refusal classification stays in testing/type.
The kernel never classifies an exception as a passed or falsified property.

Source freshness is rechecked after iterator EOF before certifying exhaustion.
Zero shrink fuel invokes no shrink callback. A child is pulled only inside the
budgeted consumer body; no tail lookahead occurs after the final allowed attempt.
`minimal?` requires observed EOF and certifies only the supplied immediate
neighborhood. POO-derived raw shrink callbacks keep their finite proper-list
contract at one boundary; their own preparation cost remains subject to the
existing graph/search budgets and process guards.

Reports retain observers for all generated trial roots and forced shrink branches,
including earlier successful trials and rejected candidates. A changed original
branch cannot become authorized merely because the final witness moved elsewhere.
Seed replay keeps those observers live throughout rerun, and the new report owns
only the rerun's observations rather than accumulating replay closure chains.
Concrete replay performs no draws, selectors or child forcing. Observer accuracy,
callback purity/termination and runtime PRNG correctness remain explicit premises.

## Decision

Extend the existing descriptor-driven property-testing protocol with finite,
state-dependent command traces. Reuse its generator objects, PRNG ownership,
strict shrinking, revision admission, reports and Reader/FUN integration.
Use `:std/test` as the downstream test runner. Do not introduce another runner,
DSL, package namespace, scheduler, module loader or serialization framework.

The first complete unit exercises declarative unique indexes and persistent table
deltas: conflicting installation, successful installation, inverse recovery,
stale collection metadata/deltas and explicit repair/retry. It provides a reusable
trace protocol plus an executable collection example, rather than one hard-coded
random test or a general runtime/FFI verification framework.

## Source basis and existing capabilities

The author's [I/O Validation and Beyond discussion](https://github.com/metareflection/poof/blob/9affa8fbbb4f12cbd98cb97f8b8b84474fc39429/poof.scrbl#L1361)
explicitly includes pseudo-random value generators and value compressors among
type-descriptor operations. His dictionary examples compose algorithms through
final-self extension points. Stateful trace generation and dependency-preserving
shrinking are proposed extensions of that direction, not algorithms claimed to
already exist in the Racket listings. The fixed-point use of the word generator
elsewhere in the paper is distinct from a pseudo-random test sampler.

| Existing owner | Reused responsibility |
| --- | --- |
| `testing/type.ss` | Typed generator/product preparation, Type/source admission, report projection and `property-action`; execution delegates to the generic modules |
| `testing/generation-graph.ss` / `testing/recursive-generation.ss` | Existing bounded recursive value generation; not replaced by a second recursion engine |
| `Type`, `List`, `Tuple`, `Union`, `Exactly`, `Enum` | Command and trace membership; no `Any` fallback |
| Existing table/index protocols | `.delta/opt`, `.apply-delta`, `invert-table-delta`, index observations and supported metadata invalidation |
| FUN / IO and `:std/test` | Composition, fixture resource lifetime and ordinary suite discovery/checks |
| `LeanPoo.Functional.PropertyTesting` | Shrink admission, descent, retained falsity, budgets and stale-evidence laws |

The audit used Gerbil commit `7b2ead60d52c3648a26e65ca149636f5ab6f39dc`
and Lean commit `7f2f71e1463b99151f23994d1b1fcc1acd5a7696`. Uncommitted
representation/cache work is outside the audit and must not be overwritten.
See the existing `generated-testing.md`, `recursive-generators.md` and
`table-indexes.md` in each repository's documentation directory.

## Scope and explicit boundaries

V1 uses finite, sequential command traces, pure reference-state transitions,
explicit logical handles and finite canonical observations. Commands are owned,
stable data values. Every trial, shrink probe and replay gets a fresh actual
fixture. Model hooks and observation callbacks must terminate and produce finite,
stable values; process watchdogs and heap limits remain necessary.

The initial oracle uses ordinary association lists and logical receipt records,
independent of the implementation's indexed table algorithms. It must not call
`.apply-delta`, index construction or inverse application to compute expectations.
An oracle is fallible: Lean proves stated source-model laws, not the complete
Scheme implementation, compiler, collector or physical memory behavior.

Concurrent scheduling, arbitrary FFI pointer graphs, universal callback synthesis,
portable closure serialization and automatic contract/law discovery are outside
this unit. The first collection adapter qualifies the pure protocol on two
existing backends. Other ownership styles require their own execution/ownership
checks; pure results alone cannot certify mutable or linear publication.

## Abstraction and implementation review

The implementation uses the existing POO `Record` contract for sampler/model/
fixture data rather than hand-written field-presence loops. `TraceGenerator`
inherits `TraceModel`, so generation and checking declare one domain.

A shared typed reference fold supports two selection policies: strict admission
rejects disabled commands; repair retires them. Both invoke the same state/result
boundary and preserve retained command order. Bounded generation carries its
state through `for/fold`; differential checking folds paired reference/actual
states and uses one escape continuation for the first mismatch. The scoped
fixture owns resource cleanup, while `property-action` uses the existing
Reader/FUN bind to hand its report to the caller's consumer.

This keeps policy separate from traversal without adding a monad, interpreter or
namespace solely for testing. Host exceptions stay errors. Invalid shrink
proposals still reach the existing budget/domain gate, rather than being hidden
by a new callback wrapper. The fixture's actual-state contract may intentionally
include expired snapshots; command preconditions and stale-version observations
remain part of the domain model.

The executable examples are `examples/collection-testing.ss` and
`t/representations/collection-testing-test.ss`. They exercise both existing RationalDict and trie
backends, including adapters deliberately broken at stale admission, index
observation, inverse installation and atomic failure. Their reference oracle uses
logical handles and ordinary lists, independent of backend mutation algorithms.


## Release readiness and abstraction review

Review date: 2026-11-02. The v0.1.2 admission covers the functional POO modules,
typed contract/collection integration and the complete PBT call chain. It is a
finite-protocol release, not a statement that every TODO or research direction
is complete. Generalized MOP constructions advance the original future work.

| Boundary | Existing mechanism retained | POO-specific responsibility |
| --- | --- | --- |
| Composition | `fun.ss`, `io.ss`, standard `compose`, ordinary closures and hygienic binding forms | Reader configuration, checked effects and report delivery |
| Public types | Existing Type/Record/Function declarations and Gerbil `using`/procedure contracts | Recursive wrapping, declared epochs, bounded membership and evidence |
| Generic PBT data | Standard private Gerbil structs, hash tables and list algorithms | Explicit domain/measure callbacks; no POO dependency in the generic kernel |
| Lazy traversal | Official `std/iter` Iterable/Iterator interfaces, `iter`, `for`, `in-coroutine` | Source authority at creation, conversion and every pull; proposal accounting |
| Prepared call layouts | Official `std/struct/lru`, standard promises and signature decoding | Bounded layout reuse without retaining arguments or renewing old epochs |
| Randomness | Invocation-owned SRFI-27 sources and opaque state checkpoints | Explicit seed ownership and dependent regeneration, without a second PRNG |
| Replay | Standard ports and reader/writer with explicit codec identity | Finite data admission, source-current handoff and exact failure priority |
| Build and tests | `defbuild-script`, standard `gerbil clean/build/test`, `:std/test` | Complete case/module receipts, heap/cancellation guards and integration assertions |

The source review inspected installed Gerbil v0.19 `std/iter/interface.ss`,
`std/iter/iterators.ss`, `std/iter/macros.ss`, `std/struct/lru.ss`, `std/func.ss`
and the core contract surface alongside the project FUN/IO implementations.
`Iterable.iter` is an application callback; the new preparation boundary corrects
the previously missing inherited authority without replacing official dispatch.
The application fixture returns the checked `Iterator` interface required by
Gerbil's compiled interface method. No parallel interface or stream library is
introduced. Functional definitions added for this fix carry their own comments.

The core PBT modules remain below 1,000 lines and keep distinct responsibilities:
generation/trees, execution/accounting, models/repair, portable replay and test
registration. Typed derivation, recursive graph discovery and Function call
layouts remain separate modules. The active production collection/type/object
modules reviewed also remain below that bound. Stateful search loops express
budget/progress control; the surrounding reusable abstraction is the existing
map/bind/sequence algebra and declaration macros, rather than a second driver.

The private recursive interaction transport still uses an erased carrier, written
`Any` inside the closed program. That transport is not a fallback inference or
public generation descriptor: graph-directed parsing, node/depth/search admission
and captured source checks authorize every public result. This release does not
claim an independent static type theorem for arbitrary intermediate host values.
It also does not claim unrestricted recursive types, arbitrary callback
termination/purity, invisible payload-mutation detection, general concurrent
linearizability, compiler/collector verification or universal performance gains.
These explicit premises must not be recorded as missing finite PBT features.

Two concrete admission defects were corrected: standard Iterable conversion now
inherits the same source scope as the surrounding action, and Scheme's push CI
now names its actual default/release branch, `master`. Lean already checks `main`.
Before squash, both exact PR heads must pass their unchanged complete workflows.
After squash, both resulting default-branch commits must pass CI again before
v0.1.2 tags/releases are created. The Lean package version and both release tags
identify the same release series; Scheme continues to use its ordinary package
and Git release identity, without an extra version manifest.

The main 2 GiB and isolated 1 GiB bounds, cancellation, complete case coverage
and natural compiler/test completion remain unchanged. Full benchmark data,
compressed archives and build products stay out of Git. Audit receipts and Git
history retain provenance; feature names, rather than phase numbers, organize
this design.

