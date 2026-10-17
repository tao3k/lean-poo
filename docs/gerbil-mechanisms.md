# Gerbil mechanisms and POO adaptation

## Scope and source basis

This audit follows the installed Gerbil 0.19 runtime used for the checks
(`1cfb032`, downstream patch `618d76f9eb72`). It inventories imports and
functional definitions in the 91 root/support Scheme modules (including `build.ss`) at the audit
baseline, then inspects the mechanism boundaries listed below. It is not a
line-by-line proof of all modules or an audit of every Gerbil library. Source
paths below are relative to the Gerbil source tree, not checkout dependencies.
The added adapter increases that module inventory to 92.

The Racket document's section 5 derives classes as type descriptors; appendix B
separates lens, object-setter/cooking and method-wrapper. It calls the full
unified protocol future work. This contract interoperability work advances that
future work; it does not turn those sketches into a proved host implementation.

## Reuse ledger

| Mechanism | Gerbil facility / inspected source | POO decision |
| --- | --- | --- |
| Predicate contracts | `gerbil/core/contract.ss`: `using`, `list-of?`, `one-of`, `in-range-inclusive?` | Replaced repeated checks in Function admission, diagnostics, refinement, metadata evidence binding, finite type admission and generator configuration. One refusal adapter preserves the published error policy. |
| Classes and interfaces | Core class-aware `using`, generated accessors; `std/interface.ss`, `std/instance.ss` | Use generated host structures for private state, and direct class-aware `using` in `examples/contract-interop.ss`. Dynamic prototype rows, descriptor validation and checked Function results remain POO operations. A host class assertion cannot recursively wrap an object graph. |
| Inheritance | `gerbil/runtime/c3.ss`: `c4-linearize` | Already reused by `object.ss`; there is no additional C4 implementation in this Scheme layer. POO still supplies lazy prototype computation, mutation guards and metadata. |
| Method dispatch | Core `defmethod` / class method machinery | Use it for host classes. `multimethod.ss` retains typed tuple dispatch, persistent revisions, negative applicability guards and selectable combinations; these are not replaced by a single host method lookup. |
| Composition | `std/func.ss`: `compose`, `rcompose`; `std/list/list.ss`: `map-in-order`, folds | Already used in IO, generalized prototypes and metadata. Existing FUN/Observation bind composes normalization before observation; replacing it with plain composition would discard its environment and sequencing protocol. |
| Persistent collections | `std/struct/rbtree.ss`, `std/iter.ss` | Already used in `prototype-map.ss` and `support/rationaldict.ss`; persistent ordered mapping and iteration reuse those implementations. `support/list.ss` traverses arbitrary pair trees, not only proper lists. |
| Tables and weak ownership | Runtime hash tables, weak keys/values | Already used by graph identity tables, `object-state.ss` and `slot-layout.ss`. POO retains source stamps, dependent invalidation and shape eligibility, rather than implementing another hash table. |
| Options / absence | Generated `some` struct in `support/option.ss` | Retain the small value protocol: `some #f` differs from absence. A default `#f` hash lookup or Boolean optional contract cannot replace it without changing callers. |
| Promise and cache | Core promise support; `std/cache.ss` allocation pools, reset/size/flush registry | Use host storage and promises where applicable. Recursive request memo owns a program identity and budget; validation caches own active-cycle state, source revisions and checked wrappers. Allocation pools do not provide these semantic invalidation laws. No second general allocation-pool implementation is introduced. |
| Concurrency and cleanup | Runtime `with-lock` / mutexes, `dynamic-wind`; `std/sync` facilities | Already used in component publication and scoped recursive coordination. Retain POO approval epochs, incarnation fences and stale-install refusal under those primitives. Generic thread helpers do not define the publication transaction. |
| Syntax and reflection | Core syntax-case, defstruct, class metadata and generated methods | Reuse host binding/expansion. `.o`, `.cc`, `.parameters`, declarations and dynamic slot reflection expose the prototype protocol; host struct metadata does not replace receiver-dependent computed slots. No new contract syntax layer is added. |
| JSON and IO | `std/encoding/json.ss`; `support/json.ss`, `io.ss` | Already delegates parsing/printing; thin wrappers select representation and compose descriptor conversion. No parser rewrite or claim of JSON parser verification. |
| Testing and generation | `std/test.ss`, host SRFI-27 random sources | Already used for assertions, isolated seeded randomness and the single-process harness. Descriptor-specific finite generation, strict shrinking and stale replay retain POO policy. Not a replacement test framework or a second PRNG. |
| Build and resources | `std/build-script`, `std/make`; bounded test runner | Existing dependency scheduler, generated test inventory, heap and wall-clock limits are retained. The new suite is one additional atomic contracts test and also runs in the complete single-process check. |

## Thin contract adapter

the companion Scheme `contract-adapter.ss` exports one function, `check-contract`, and no syntax,
registry or descriptor type. The user predicate is evaluated exactly once,
**outside** exception translation. Gerbil `using` receives its result and owns
the truthiness guard. Its body only returns the original value. Only a
`ContractViolation` created by this local guard is translated through the
caller's original refusal callback. Predicate, normalizer, Function body and
consumer exceptions—including their own `ContractViolation` objects—propagate
unchanged. A broad handler around the whole workflow would be incorrect.

POO `TypeError`, controlled `TypeRefusal`, legacy messages and irritants remain
boundary policy. This is why public POO parameters do not simply change their
failure type to Gerbil `ContractViolation`. New host-specific code can use
`using` directly, as the typed observation sink does.

Core range rules require fixnums. They are used only for small capped ranges
(depth, node count and work budgets); every previously admitted exact integer
in those intervals is a fixnum. Arbitrary `Integer`/`UInt` domains and shrink
measures keep their unbounded integer checks. Predicates preserve Scheme
truthiness rather than requiring a Boolean; declarative metadata deliberately
keeps its separate Boolean-only decision policy.

## Ordered integration

`examples/contract-interop.ss` composes the existing inferred recursive service
row, nested Function wrappers and whole-object `refine` with a Gerbil typed
consumer. The publication entry point creates evidence from the **current
checked subject**, then uses the existing exact `bind-evidence` publisher.
A previous checked object or context cannot approve a newly normalized subject.
Observation side effects are not rolled back by a later evidence refusal.

Two internal bindings now use explicit `let` to enforce phase order: callee
recognition precedes signature metadata forcing; structural object refusal
precedes child normalization. Regressions observe zero metadata/child callbacks
on those rejected paths, not merely the final exception type.

The regression suite also checks truthy results, one predicate invocation,
exception identity, old error messages, large invalid budgets, recursive method
argument refusal, multiple return values and no CaseFunction fallback after a
body error. Full tests continue to cover cyclic graphs, rows, inheritance,
containers, shared revisions, refinements and evidence independently.

## Lean boundary

`Functional.ContractAdaptation` proves delegated/direct guard equivalence for
all supplied predicate outcomes and ordered finite batches. Workflow laws prove
refusal before normalization, delivery of checked values, and preservation of
predicate and normalization errors. Consumer errors follow the same whole
workflow equivalence. `Examples/ContractAdaptation.lean` supplies checked method,
state/multiple-result and host-error controls.

The premise is the observed core guard behavior and supplied callback semantics.
These are not compiler, runtime, arbitrary callback termination, continuation
or concurrency proofs. Scheme tests exercise the real macro and effects.
A later optimization must separately measure successful calls and refusal paths;
this refactor makes no speedup claim.
