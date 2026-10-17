# Gerbil mechanisms and POO protocols

## Scope and source basis

This audit follows the installed Gerbil 0.19 runtime used for the checks
(`1cfb032`, downstream patch `618d76f9eb72`). It inventories imports and
functional definitions in the 91 root/support Scheme modules (including `build.ss`) at the audit
baseline, then inspects the mechanism boundaries listed below. It is not a
line-by-line proof of all modules or an audit of every Gerbil library. Source
paths below are relative to the Gerbil source tree, not checkout dependencies.
The independent contract module has been removed; the inventory remains 91.
The small refusal-policy function lives in the existing `support/base.ss`.

The Racket document's section 5 derives classes as type descriptors; appendix B
separates lens, object-setter/cooking and method-wrapper. It calls the full
unified protocol future work. This contract interoperability work advances that
future work; it does not turn those sketches into a proved host implementation.

## Reuse ledger

| Mechanism | Gerbil facility / inspected source | POO decision |
| --- | --- | --- |
| Predicate contracts | `gerbil/core/contract.ss`: `using`, `list-of?`, `one-of`, `in-range-inclusive?` | Replaced repeated checks in Function admission, diagnostics, refinement, metadata evidence binding, finite type admission and generator configuration. The existing support module preserves the published refusal policy. |
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

## Standard contracts and POO refusal policy

Gerbil core `using` / ContractRules and `std/error` `check-argument` remain the
contract mechanisms. There is no POO contract namespace, facade or alternate
contract syntax. `support/base.ss` contains `require-value` only for existing POO
boundaries whose refusal policies differ from the standard error family.

The predicate is evaluated exactly once, outside the local failure handler.
`using` owns the truthiness guard; its body only returns the original value.
Only that local guard's `ContractViolation` is translated by the supplied refusal
callback. Predicate, normalizer, Function body and consumer exceptions propagate
unchanged, including their own `ContractViolation` objects. Standard
`check-argument` is not shadowed or redefined. New host-specific code uses the
standard contracts directly.

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

The existing `Functional.Validation` namespace proves delegated/direct guard equivalence for
all supplied predicate outcomes and ordered finite batches. Workflow laws prove
refusal before normalization, delivery of checked values, and preservation of
predicate and normalization errors. Consumer errors follow the same whole
workflow equivalence. `Examples/ContractChecks.lean` supplies checked method,
state/multiple-result and host-error controls.

The premise is the observed core guard behavior and supplied callback semantics.
These are not compiler, runtime, arbitrary callback termination, continuation
or concurrency proofs. Scheme tests exercise the real macro and effects.
A later optimization must separately measure successful calls and refusal paths;
this refactor makes no speedup claim.

## Class/interface, container and cache audit

The follow-up source inspection covers `std/instance.ss`, `std/interface.ss`,
`std/iter/{api,interface,iterators}.ss`, `std/vector/vector.ss`,
`std/list/list-builder.ss`, `std/hash/misc.ss`, runtime HashTable and
`std/cache.ss`, against POO class validation, table iteration, shape layouts and
construction/recursive/feedback caches.

Confirmed repetitions removed:

- `construction-cache.ss` now uses standard `hash-ref/default` for all three
  source/lookup fallbacks instead of a key-exists probe followed by another
  lookup. The standard HashTable interface owns the lookup. Stored `#f` is a
  hit; only missing keys invoke the fallback. Unknown-source callbacks, original
  exceptions, same-owner retention and source-bound selective rebuild remain.
- `slot-layout.ss` uses `hash-ensure-ref` for canonical shapes. Shape creation
  and insertion use the standard missing-key operation; the table retains its
  weak values. Class-aware `using` handles generated accessors and field writes
  for the access-site record. Owner/revision/layout/index guards and per-receiver
  cells remain POO policy. Index zero and cell value false remain valid.
- List/Tuple shape diagnostics use `with-list-builder`, avoiding a temporary
  list of child lists and a final flattening pass. Proper finite diagnostic
  lists are the callback premise. Ordered traversal uses `for` and
  `vector-for-each/index`; values, paths and issue multiplicity are unchanged.
- `validate-class` and `validate-container` use explicit binding after the shape
  gate so no child normalizer can run before structural refusal.

Retained after source comparison:

- Gerbil's iterator API in this runtime has no exported mapping combinator.
  `table.ss` already implements its small mapper with the standard `Iterator`
  interface. Keep it rather than inventing an `in-map` import or adding eager
  collection/coroutine state. `examples/service-collection.ss` reuses it and
  registers a generated host class with standard `std.instance` / `Iterable`.
  Each pull uses the existing checked FUN action; no second iterator engine.
- `vector-map/index` explicitly leaves callback order unspecified and currently
  maps from right to left. It cannot replace ordered validators. The regression
  observes callback order as well as final container contents.
- `rationaldict` already delegates persistent storage and folds to standard
  RBTree; its option, lower-bound iteration and supplied value equality are POO
  table semantics. Replacing it with mutable HashTable or structural tree equality
  would change persistence or comparator behavior.
- `std/cache` supplies `CacheOps` size/flush and object allocation pools. Neither
  operation certifies source stamps, guarded recursion, SCC reuse or approvals.
  Construction/feedback/recursive caches keep these policies over standard
  tables. Published immutable state is not repurposed as a mutable pool object.

The integrated collection example observes inherited Record methods through a
standard Iterable, then observes new raw rows from a selectively revised source
cache. Failed new admission leaves the old snapshot usable. It does not cache
normalized approvals or roll back prior consumer effects. Regressions also check
lazy iterator construction, exact error identity, shape guards and stored absence.

Lean `Functional.CacheLookup` adds laws in the existing `ConstructionCache`
namespace: lazy present/missing selection, stored absence, ensure-hit retention,
failed-build retention, frame preservation and no reconstruction after insertion.
`Validation.gatherIssues_eq_flatMap` proves ordered issue collection equivalence.
The small law modules avoid loading the full generalized MOP merely to check
lookup laws. `Examples/ServiceCollection.lean` composes these laws with existing
ordered validation. Host hash equality, standard interface dispatch/iteration,
weak-reference reachability and callback behavior remain premises, not kernel
proofs of Gerbil or GC. Resource guards and complete checks remain unchanged.

## Inheritance, dispatch, syntax and reflection audit

This follow-up inspects runtime `c3.ss` (`c4-linearize`, `c4-linearize*`,
`c4-compute-class-slots`), expander `stx.ss` (`identifier-list?`), core
`mop.ss` / `contract.ss`, and standard list deduplication against `object.ss`,
`reflection.ss`, `.defgeneric`, method combination and sparse multi-dispatch.

Confirmed repetitions removed:

- `compute-precedence-list!` calls core `c4-linearize*` directly. The previous
  core `c4-linearize` compatibility wrapper only reversed the singleton head and
  wrapped the parents in one list. Those exact arguments now go to the primary
  API. The POO active-path guard, checked inherited hooks, diagnostic naming and
  revision invalidation remain unchanged. Tests compare both actual core APIs
  and the public POO result on a shared diamond.
- `merge-super-slots` uses ordered standard `append` and
  `delete-duplicates/hash`, with the same symbolic-identity table and explicit
  `from-end?: #t`. Ancestor-first inventory order and most-specific method order
  remain distinct. Same-printed uninterned symbols retain distinct identities.
  A regression rejected this release's `append-map` for this path because its
  actual order differs; the original order expectation is retained.
- `reflect-slots` uses standard first-key deduplication instead of a handwritten
  seen/filter loop. It still resolves the most-specific declaration **before**
  visibility filtering, so a private child cannot reveal a public ancestor.
  Hidden metadata getter order is retained by the existing outer fold. Instance
  values remain unforced during reflection; metadata revision uses the current
  descriptors and invalidates registered receivers normally.
- Lexical slot binding deduplication uses the same standard deduplicator with
  `bound-identifier=?` and an explicit constant hash. A printed-datum hash would
  be invalid for binding identity. This preserves first representatives and the
  original quadratic worst case; no compile-time speedup is asserted. A real
  macro control distinguishes same-spelled identifiers from different scopes.
- Object `bind:` admission delegates to core `identifier-list?`. The reserved
  option-prefix grammar, source errors and local-slot binding rules remain POO
  syntax. Dotted/nonidentifier lists refuse during actual expansion.
- Contribution/forwarding/Simula constructors, simple-policy Boolean checks and
  guarded multi-dispatch reuse the existing support refusal policy over core
  `using`. The actual predicate or method body is outside local translation;
  legacy errors, original exceptions and strict Boolean decisions are retained.

Retained after comparison:

- Core class methods do not supply this library's runtime prototype tuples,
  persistent generic revisions, qualifier policies, current-call guards,
  negative watches, receiver-dependent computed slots or nested cache transport.
  Sparse multi-dispatch and the POO `.defgeneric` operation remain. No class
  method cache is treated as a current negative-assumption certificate.
- Standard host class slots are fixed metadata; `c4-compute-class-slots` also
  inserts a class field and has its own layout order. It cannot replace the POO
  symbolic inventory or public/private declaration catalogs.
- Core lambda expansion owns legal host arguments and default evaluation.
  `support/syntax.ss` retains the small forwarder for the currently supported
  ordinary required/optional/keyword/rest grammar. No public standard routine
  with that exact forwarding/failure policy was identified; private compiler
  signature helpers are not imported as a substitute. Arbitrary annotated host
  signatures and universal macro-expander equivalence are not claimed.
- Method qualifier grouping and `next` chains retain their existing fold and
  callback order. A generic filter/map rewrite would need a separate effect-order
  argument; no body/default/guard is speculatively evaluated for reflection.

`examples/declared-methods.ss` extends its existing shared inheritance family
with a private label override and an optional/keyword/rest summary method. The
existing FUN Reader returns both charge and summary from fresh receiver data;
method effects stay ordered and current context is not cached. Nine additional
cases in `t/library-reuse-test.ss` cover core C4 equivalence, symbolic and lexical
identity, hidden override revision, actual syntax rejection, legacy constructor
refusals, per-call guards/negative assumptions and the integrated multi-value
observation. No new Scheme module or namespace is introduced.

Lean adds five stable-selection/inventory laws in existing
`Functional.Parameters`, and three public-selection laws in existing
`Prototype.DescriptorReflection` (`Object/DeclarationOrder.lean`). Examples stay
in root `Examples/Parameters.lean` and its existing namespace. The standard
hash comparator and C4/expander behavior are host premises checked by Scheme
controls; these laws prove the finite semantic policy, not Gerbil compilation,
GC, arbitrary effects or concurrency. Existing method-combination and hook laws
remain the corresponding continuation/order proofs. Resource limits and the
complete local/CI check sets remain mandatory.

Cancellation verification also covers a blocked progress pipe: after stopping
owned child groups, the atom supervisor exits with status 143 without joining
executor threads that can no longer drain output. A subprocess regression fails
on the previous implementation with a bounded timeout and passes after the fix.
Existing queued-launch cancellation, process-group and complete-check tests remain;
heap, time, heartbeat and concurrency budgets are not widened.

### Whole-protocol selection through core `ormap`

The active Gerbil runtime's public `ormap` (`gerbil/runtime/util.ss`) returns
the exact first non-false callback result, visiting the input from left to right
and stopping immediately on success or exception. `object-protocol` now uses it
directly instead of duplicating that traversal. The input remains the existing
checked C3 precedence list; no linearization, dependency edge, invalidation rule
or hook dispatcher is replaced.

Selection chooses **one complete protocol object**. An empty protocol on the
first branch shadows a later branch's hooks; missing hooks use the existing
engine continuation. Removing that branch's protocol permits the current suffix
to supply one. Parent reordering and protocol replacement go through existing
checked mutation operations and invalidate the join. The inherited-services
example adds `protocol-action`, composing that mutation and public observations
through the existing FUN Reader operation.

Regression controls exercise actual callback order and suffix non-evaluation,
exception identity, whole-object shadowing, removal/reordering, shared-join
invalidation, private-field non-demand and sealed-source refusal. Lean's
`Functional/ProtocolSelection.lean` uses `List.findSome?` in the existing
`Functional.InheritedMOP` namespace: first selection, absent-source delegation,
all-absent characterization and selected-prefix stability are proved. These
are pure lookup laws; runtime effects, host pointer identity, C3 correctness and
GC are not inferred from them. The generalized MOP remains an extension of the
article's stated future work.

The deeper dispatch/syntax/reflection pass retains the following POO policies:

* `.defgeneric` resolves a missing-slot fallback only for the original receiver
  and slot. Core lambda owns optional/keyword/default admission; the small
  forwarding helper passes the resulting bindings without rerunning defaults.
  Compiler-private signature utilities are not a public replacement.
* Effective-method caches retain source identity and current applicability
  guards. An ordinary host method cache does not supply negative-assumption
  revalidation, qualifier interpretation or nested cache transport.
* Reflection selects current first metadata before visibility checks, and its
  complete catalog traversal preserves descriptor errors and getter order.
  An early-exit lookup would silently skip these observations.

No additional namespace, contract DSL, host dispatcher or performance claim is
introduced. This audit closes the confirmed traversal duplication; it does not
mark unrelated TODO items complete.
