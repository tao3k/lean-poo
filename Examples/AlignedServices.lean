import LeanPoo.Object.MultimethodCombination
import LeanPoo.Functional.ContractFamily
import LeanPoo.Functional.CyclicAccess
import LeanPoo.Functional.ServiceBundle
import LeanPoo.Object.SimplePolicies
import LeanPoo.Object.MethodCombinationSemantics
import LeanPoo.Object.SimpleCombinationSemantics

/-! Concrete Appendix B method combinations and shared invariant metadata.
The generalized joint-publication and cost-budget composition advances future
work. These proofs cover functional semantics and supplied operation budgets;
they make no claim about Scheme compilation, elapsed time or predicted GC. -/
namespace LeanPoo.Examples.AlignedServices
open Functional.DeclarativeMetadata
open Functional.ContractFamily.PreparationCosts
open Object.MethodCombination

/-- Reservation arithmetic combines a current capacity item and a debit item;
around checks the current view before invoking that reduction. -/
def remaining (capacity : Int) : SimpleMethods Int (Except String) Int Int where
  items := [fun units => .ok (-units), fun _ => .ok capacity]
  around := [fun next units => if 0 < units ∧ units ≤ capacity then next () else .error "capacity"]

/-- The standard primary chain computes the same arithmetic with the original
argument preserved by next; a shared around check rejects over-capacity calls. -/
def reservation (capacity : Int) : Methods Int (Except String) Int where
  primary := [fun next _ => next (), fun _ units => .ok (capacity - units)]
  around := [fun next units => if 0 < units ∧ units ≤ capacity then next () else .error "capacity"]

/-- Both native service-combination examples have the same checked result for
all valid capacities/units, while using different existing method constructs. -/
theorem reservation_equivalent (capacity units : Int) (positive : 0 < units) (fits : units ≤ capacity) :
    effective (reservation capacity) (fun _ => .error "missing") units =
      simpleEffective (SimplePolicy.sum Int) (remaining capacity) units := by
  simp [effective, reservation, callChain, runSides, simpleEffective, remaining,
    runSimpleTail, SimplePolicy.sum, positive, fits, Int.sub_eq_add_neg, Int.add_comm, bind, Except.bind, pure, Except.pure]

/-- Around refusal occurs before either the standard or simple method bodies. -/
theorem reservation_refused (capacity units : Int) (invalid : ¬ (0 < units ∧ units ≤ capacity)) :
    effective (reservation capacity) (fun _ => .error "missing") units = .error "capacity" ∧
      simpleEffective (SimplePolicy.sum Int) (remaining capacity) units = .error "capacity" := by
  simp [effective, reservation, callChain, simpleEffective, remaining, invalid]

/-- Supplied operation weights for selector preparation; these are illustrative
counts rather than embedded timings or inferred future workload frequencies. -/
def selectorPrices : SelectionCacheCosts := ⟨2,1⟩

/-- The relevant horizon counts actual changed-context preparation entries.
A large total number of publications does not imply a large value here. -/
def horizon (calls : Nat) : SelectionBudget := ⟨calls,0,0,0⟩

/-- Cold preparation cannot amortize setup; stable repeated misses can. -/
theorem cold_and_stable : selectorPrices.choose 4 (horizon 1) = .dynamic ∧
    selectorPrices.choose 4 (horizon 64) = .cached := by decide

/-- Every changed-support fallback and a conservative excess-GC budget can
reverse that choice; setup and guards alone are insufficient admission grounds. -/
theorem fallback_and_gc : selectorPrices.choose 4 ⟨64,64,0,0⟩ = .dynamic ∧
    selectorPrices.choose 4 ⟨64,0,3,100⟩ = .dynamic := by decide

/-- Shared expansion, descriptor construction, binding and joint approval remain
charged in base. The selector bound applies only under the supplied cost budget. -/
theorem complete_budget (base : Nat) (budget : SelectionBudget) :
    base + selectorPrices.selectedBudget 4 budget ≤ base + selectorPrices.dynamicBudget 4 budget :=
  selectorPrices.workflow_bound 4 base budget

/-- A nonzero policy-configuration cost is admissible only when explicitly
covered by the stable selector saving; it is not hidden in a warm template. -/
theorem configured_stable (base : Nat) :
    base + 5 + selectorPrices.selectedBudget 4 (horizon 64) ≤
      base + selectorPrices.dynamicBudget 4 (horizon 64) :=
  selectorPrices.configuration_covered 4 5 base (horizon 64) (by decide)

/-- Specializing a reusable invariant check record changes only current meaning;
the exact contract identity law transfers every existing invocation failure law. -/
theorem shared_checks (source : Contract Atom Args Result) (checks : source.Checks)
    (meaning : Atom → Args → Result → Prop)
    (decision : ∀ atom args result, Decidable (meaning atom args result)) :
    checks.specialize meaning decision = source.withMeaning meaning decision :=
  checks.specialize_eq meaning decision

#print axioms reservation_equivalent
#print axioms reservation_refused
#print axioms complete_budget
#print axioms configured_stable
#print axioms shared_checks
end LeanPoo.Examples.AlignedServices

/-! Request enrichment and staged preflight using existing combination constructs.
This extends the reference's open combination direction. Functional/effect laws
and supplied operation budgets do not certify native compiler or GC behavior. -/
namespace LeanPoo.Examples.AlignedServices
open Object.MethodCombination Functional.ContractFamily.PreparationCosts

/-- Current service context; invoice is a real dependency of enriched requests. -/
structure View where
  capacity : Int
  invoice : String
  released : Bool
  deriving Repr, DecidableEq

/-- Typed forwarded request separates its business payload from fixed dispatch. -/
structure Request where
  units : Int
  invoice : String
  approved : Bool
  deriving Repr, DecidableEq

/-- Around refreshes current invoice, primary approves, inherited arithmetic uses
that enriched payload. No continuation can replace the dispatch String. -/
def forwarding (view : View) : ForwardMethods String Request (Except String) Int where
  around := [fun next call =>
    if view.released ∧ 0 < call.2.units ∧ call.2.units ≤ view.capacity then
      next (some {call.2 with invoice := view.invoice}) else .error "unavailable"]
  primary := [fun next call => next (some {call.2 with approved := true}),
    fun _ call => if call.1 = "reserve" ∧ call.2.invoice = view.invoice ∧ call.2.approved then
      .ok (view.capacity - call.2.units) else .error "stale"]

/-- Enrichment accepts a stale incoming invoice only after replacing it with the
CURRENT one. Arithmetic is unchanged and every next retains dispatch identity. -/
theorem forwarding_current (view : View) (request : Request)
    (released : view.released = true) (positive : 0 < request.units) (fits : request.units ≤ view.capacity) :
    forwardEffective (forwarding view) (fun _ => .error "missing") ("reserve",request) =
      .ok (view.capacity - request.units) := by
  simp [forwardEffective, forwarding, callForwardChain, released, positive, fits,
    bind, Except.bind, pure, Except.pure]

/-- Revocation stops before invoice/primary processing; no descendant runs. -/
theorem forwarding_revoked (view : View) (request : Request) (revoked : view.released = false) :
    forwardEffective (forwarding view) (fun _ => .error "missing") ("reserve",request) = .error "unavailable" := by
  simp [forwardEffective, forwarding, callForwardChain, revoked]

/-- Record the payload seen at each phase without changing it. This mirrors the
native guard/around/primary/after regression control using explicit effect state. -/
def observe (phase : String) (payload : Int) : EStateM String (List (String × Int)) Unit :=
  fun trace => .ok () (trace ++ [(phase,payload)])

/-- Around changes the whole inner request; a primary replacement is local to its
suffix, while after still observes the around-modified entry payload. -/
def tracedForward : ForwardMethods String Int (EStateM String (List (String × Int))) Int where
  around := [fun next call => next (some (call.2 + 10))]
  before := [fun call => observe "before" call.2]
  primary := [fun next call => next (some (call.2 + 1)),
    fun _ call => do observe "base" call.2; pure call.2]
  after := [fun call => observe "after" call.2]

/-- Exact phase-local payload and returned state for every initial payload. -/
theorem forwarding_payload_scope (dispatch : String) (payload : Int) :
    forwardEffective tracedForward (fun _ => throw "missing") (dispatch,payload) [] =
      .ok (payload + 11) [("before",payload+10),("base",payload+11),("after",payload+10)] := by
  simp [forwardEffective, tracedForward, callForwardChain, observe,
    bind, EStateM.bind, pure, EStateM.pure, Int.add_assoc]

/-- A private component sees the old closed input plus current invoice, rather
than an untracked full-view capture. Equality necessarily preserves both parts. -/
def enrichedInput (closed : Input) (invoice : String) := (closed,invoice)

/-- Changing only invoice cannot justify reusing the enriched reserve generic. -/
theorem enrichedInput_invoice (closed₁ closed₂ : Input) (invoice₁ invoice₂ : String)
    (same : enrichedInput closed₁ invoice₁ = enrichedInput closed₂ invoice₂) : invoice₁ = invoice₂ :=
  congrArg Prod.snd same

/-- Superclass admission controls whether the specialized arithmetic executes. -/
def inherited (view : View) : List (SubMethod Int (Except String) Int) :=
  [fun _ units => .ok (view.capacity - units),
   fun inner units => if view.released ∧ 0 < units ∧ units ≤ view.capacity then inner () else .error "unavailable"]

/-- General-first inner control reaches the descendant exactly under admission. -/
theorem inherited_current (view : View) (units : Int)
    (released : view.released = true) (positive : 0 < units) (fits : units ≤ view.capacity) :
    innerChain (inherited view) (fun _ => .error "missing") units = .ok (view.capacity - units) := by
  simp [innerChain, inherited, callChain, released, positive, fits]

/-- One observable prefix/suffix action retains executed effects on failure.
Atomic publication is a separate owner; these effects are not rolled back here. -/
def stage (name : String) (valid : Bool) : EStateM String (List String) Unit := fun trace =>
  if valid then .ok () (trace ++ [name]) else .error "refused" (trace ++ [name])

/-- Two-stage ordered preflight, specific-first in C4 input order.
Invoice is typed String here; native reconstruction separately validates its Type. -/
def preflight (view : View) : List (SimulaBody Int (EStateM String (List String))) :=
  [⟨fun units => stage "capacity" (decide (units ≤ view.capacity)), fun _ => stage "invoice" true⟩,
   ⟨fun units => stage "positive" (decide (0 < units)), fun _ => stage "release" view.released⟩]

/-- Accepted preflight has exact general-first prefixes and specific-first suffixes. -/
theorem preflight_current (view : View) (units : Int) (trace : List String)
    (released : view.released = true) (positive : 0 < units) (fits : units ≤ view.capacity) :
    simulaEffective (preflight view) units trace =
      .ok () (trace ++ ["positive","capacity","invoice","release"]) := by
  simp [preflight, simulaEffective_pair, stage, released, positive, fits,
    bind, EStateM.bind, List.append_assoc]

/-- A refused final release retains the executed trace; the enclosing publisher
must retain its old admitted version instead of exposing an unapproved successor. -/
theorem preflight_revoked (view : View) (units : Int) (trace : List String)
    (revoked : view.released = false) (positive : 0 < units) (fits : units ≤ view.capacity) :
    simulaEffective (preflight view) units trace =
      .error "refused" (trace ++ ["positive","capacity","invoice","release"]) := by
  simp [preflight, simulaEffective_pair, stage, revoked, positive, fits,
    bind, EStateM.bind, List.append_assoc]

/-- Illustrative check-preparation operation weights, independent of measured CPU. -/
def checkPrices : TemplateCosts := ⟨2,1,2⟩

/-- Cold and tie cases keep fresh checks; supported repeated use can amortize sharing. -/
theorem check_modes : checkPrices.choose 1 = .fresh ∧ checkPrices.choose 2 = .fresh ∧
    checkPrices.choose 64 = .shared := by decide

/-- Both check modes retain the common construction/binding/approval base.
Only supplied operation costs are bounded; the wrapper still performs every check. -/
theorem complete_check_budget (uses base : Nat) :
    base + checkPrices.selectedTotal uses ≤ base + checkPrices.freshTotal uses :=
  Nat.add_le_add_left (checkPrices.selected_bound uses) base

/-- Descriptor reuse and selector caching have separate horizons and costs:
these service weights amortize shared checks but never justify cached selection. -/
theorem sustained_modes : checkPrices.choose 64 = .shared ∧ selectorPrices.choose 1 (horizon 64) = .dynamic := by decide

/-- A nonzero check-policy fee cannot be amortized by a single-use fresh mode.
Callers already knowing the cold case can use the existing ordinary source. -/
theorem cold_configuration_unpaid (fee : Nat) (positive : 0 < fee) :
    ¬ (fee + checkPrices.selectedTotal 1 ≤ checkPrices.freshTotal 1) := by
  change ¬ (fee + 2 ≤ 2)
  omega

/-- Counts validation sites: six invariant domain checks plus the fallback bound
are hoisted, one selection-cost domain check remains per callback entry. These
are site counts, not allocation totals, native cycles or predicted GC costs. -/
def validationPrices : TemplateCosts := ⟨7,1,8⟩

/-- For at least one use, hoisted validation-site work is bounded by validating
all seven numeric domains and fallback relation again on every entry. -/
theorem validation_sites (uses : Nat) (nonempty : 1 ≤ uses) :
    validationPrices.sharedTotal uses ≤ validationPrices.freshTotal uses := by
  simp only [TemplateCosts.sharedTotal, TemplateCosts.freshTotal, validationPrices]
  omega

#print axioms forwarding_current
#print axioms enrichedInput_invoice
#print axioms forwarding_payload_scope
#print axioms inherited_current
#print axioms preflight_current
#print axioms preflight_revoked
#print axioms complete_check_budget
#print axioms validation_sites
#print axioms sustained_modes
#print axioms cold_configuration_unpaid
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
open Object Object.MethodCombination Functional.ContractFamily.PreparationCosts

/-- Typed child cache owned by the reserve workflow; method results remain effects. -/
abbrev PreflightCache := PreparedMultimethod Int (SimulaBody Int (EStateM String (List String)))
  (Int → EStateM String (List String) Unit) (EStateM String (List String) Unit)

/-- Prepared Simula request validator, reusing the exact prefix/suffix bodies of
preflight. The finite example keeps the same explicit Reserve/Object C4 shape. -/
def preparedPreflight (view : View) :=
  let seed := Multimethod.preparedSimula (M := EStateM String (List String)) 1
    (fun (_ : Int) => [["Reserve", "Object"]])
  (preflight view).reverse.foldl (fun current body =>
    (current.contribute [.any] body).toOption.getD current) seed

/-- Nested leaf exposes the prepared child action's success/failure explicitly;
only a successful preflight returns its immutable cache successor to reserve. -/
def invokePreflight (units : Int) (child : PreflightCache) : Except String (List String × PreflightCache) := do
  let (action, next) ← (child.call units).mapError (fun _ => "dispatch")
  match action [] with
  | .ok _ trace => return (trace, next)
  | .error error _ => .error error

/-- Reserve owns a preflight cache rather than capturing a value-only child in
its method body. The outer arity/signature is independent of the child state. -/
def nestedPreflight (view : View) :=
  let child := preparedPreflight view
  let outer := PreparedMultimethod.create 1 (fun (_ : Int) => [["Reserve", "Object"]])
    (fun (methods : Array (Int → PreflightCache → Except String (List String × PreflightCache))) =>
      (methods[0]?).getD (fun _ _ => .error "missing"))
    (fun method units => method units)
  ({ outer := (outer.register [.any] invokePreflight).toOption.getD outer, child } :
    NestedMultimethod Int _ _ _ String (List String))

/-- Two requests use the returned owner; the second request carries fresh
arguments through an already prepared outer AND child cache. -/
def nestedRequests (view : View) (first second : Int) : Except String (List String) := do
  let (_, warm) ← ((nestedPreflight view).call first).mapError (Sum.elim (fun _ => "dispatch") id)
  let (trace, _) ← (warm.call second).mapError (Sum.elim (fun _ => "dispatch") id)
  return trace

/- Concrete accepted/rejected requests exercise actual sparse resolution,
preparation, nested successor transport and Simula prefixes/suffixes together. -/
#guard (nestedRequests ⟨10,"invoice:1",true⟩ 2 3).toOption ==
  some ["positive","capacity","invoice","release"]

/- A failed second prefix returns no nested owner; it cannot expose the tentative
prepared outer cache. Native tests additionally retain the exact old publisher. -/
#guard match nestedRequests ⟨10,"invoice:1",true⟩ 2 20 with
  | .error "refused" => true
  | _ => false

/-- Declare the same C4 shape at both existing cache levels. The child and outer
methods are complete before preparation; neither body runs during this phase. -/
def prepareNestedPreflight (view : View) := do
  let owner := nestedPreflight view
  let child ← owner.child.prepareShape [["Reserve", "Object"]]
  let outer ← owner.outer.prepareShape [["Reserve", "Object"]]
  return { owner with child, outer }

/-- Admission-style probes discard returned owners. Precompiled definitions can
be reused by these probes without sharing results or skipping current checks. -/
def preparedProbes (view : View) (first second : Int) : Except String (List String × List String) := do
  let owner ← (prepareNestedPreflight view).mapError (fun _ => "prepare")
  let (firstTrace, _) ← (owner.call first).mapError (Sum.elim (fun _ => "dispatch") id)
  let (secondTrace, _) ← (owner.call second).mapError (Sum.elim (fun _ => "dispatch") id)
  return (firstTrace, secondTrace)

/- These execute actual prepared nested calls, including rejection on fresh
arguments and changed source context. Generic cache/provenance laws are proofs. -/
#guard (preparedProbes ⟨10,"invoice:1",true⟩ 2 3).toOption == some
  (["positive","capacity","invoice","release"], ["positive","capacity","invoice","release"])
#guard match preparedProbes ⟨10,"invoice:1",true⟩ 2 20 with
  | .error "refused" => true
  | _ => false
#guard match preparedProbes ⟨20,"invoice:2",false⟩ 2 3 with
  | .error "refused" => true
  | _ => false

/-- View-independent Simula method definition. The complete current view travels
in the typed argument row, so cached code contains no previous capacity/invoice
or release value. Native Object argument validation is an additional runtime cost. -/
def contextPreflight : List (SimulaBody (Int × View) (EStateM String (List String))) :=
  [⟨fun args => stage "capacity" (decide (args.1 ≤ args.2.capacity)), fun _ => stage "invoice" true⟩,
   ⟨fun args => stage "positive" (decide (0 < args.1)), fun args => stage "release" args.2.released⟩]

/-- Passing the current view explicitly reproduces the original view-specialized
prefix/suffix computation, for every argument and every success/failure trace. -/
theorem contextPreflight_equivalent (view : View) (units : Int) :
    simulaEffective contextPreflight (units, view) = simulaEffective (preflight view) units := rfl

/-- The cached context-independent program checks the CURRENT context, including
revocation. No earlier successful view can authorize a later revoked request. -/
theorem contextPreflight_revoked (view : View) (units : Int) (trace : List String)
    (revoked : view.released = false) (positive : 0 < units) (fits : units ≤ view.capacity) :
    simulaEffective contextPreflight (units, view) trace =
      .error "refused" (trace ++ ["positive","capacity","invoice","release"]) := by
  rw [contextPreflight_equivalent]
  exact preflight_revoked view units trace revoked positive fits

/-- One immutable prepared child definition can serve arbitrary typed current
views. It shares executable method data and negative applicability, not results. -/
def contextPreflightGeneric :=
  let seed := Multimethod.preparedSimula (M := EStateM String (List String)) 1
    (fun (_ : Int × View) => [["Reserve", "Object"]])
  let defined := contextPreflight.reverse.foldl (fun current body =>
    (current.contribute [.any] body).toOption.getD current) seed
  defined.prepareShape [["Reserve", "Object"]]

/-- Exercise actual sparse prepared dispatch against a newly passed view. -/
def contextPreflightRequest (view : View) (units : Int) : Except String (List String) := do
  let generic ← contextPreflightGeneric.mapError (fun _ => "prepare")
  let (action, _) ← (generic.call (units, view)).mapError (fun _ => "dispatch")
  match action [] with
  | .ok _ trace => .ok trace
  | .error error _ => .error error

/- Closed controls complement the universal view-conversion/cache invariants. -/
#guard (contextPreflightRequest ⟨20,"invoice:2",true⟩ 15).toOption ==
  some ["positive","capacity","invoice","release"]
#guard match contextPreflightRequest ⟨10,"invoice:1",true⟩ 15 with
  | .error "refused" => true
  | _ => false
#guard match contextPreflightRequest ⟨20,"invoice:3",false⟩ 2 with
  | .error "refused" => true
  | _ => false

/-- Illustrative primitive prices keep cold construction and nested transport
visible; empirical Scheme CPU/GC is independently measured by paired children. -/
def effectivePrices : EffectiveCosts := ⟨9,5,2,3,1,4,10⟩

/-- Only a supported repeated horizon amortizes the combined cache setup.
Guard-heavy or excess-GC schedules can reverse the decision. -/
theorem effective_modes : (effectivePrices.prices ⟨1,1,1,0,0⟩).choose 1 = .fresh ∧
    (effectivePrices.prices ⟨32,1,1,0,0⟩).choose 32 = .shared ∧
    (effectivePrices.prices ⟨32,1,1,0,100⟩).choose 32 = .fresh := by decide

/-- Cold effective caching alone does not amortize setup; a complete publisher
can nevertheless save enough carrier construction to justify the prepared path.
These supplied counts illustrate the unequal-base rule, not measured CPU. -/
theorem cold_publication_mode :
    (effectivePrices.prices ⟨1,1,1,0,0⟩).choose 1 = .fresh ∧
    effectivePrices.chooseWorkflow ⟨1,1,1,0,0⟩ 50 30 = .shared := by decide

/-- With one discarded admission miss and one real first entry, construction
can compile once instead of twice. Without probes or with unused declarations,
setup is not automatically paid; excess GC can also reverse the choice. -/
theorem shape_preparation_modes :
    (⟨1,1,1,2,0⟩ : ShapePreparationBudget).choose effectivePrices 0 0 1 = .shared ∧
    (⟨1,0,1,1,0⟩ : ShapePreparationBudget).choose effectivePrices 0 0 1 = .fresh ∧
    (⟨8,1,1,2,0⟩ : ShapePreparationBudget).choose effectivePrices 0 0 1 = .fresh ∧
    (⟨1,1,1,2,100⟩ : ShapePreparationBudget).choose effectivePrices 0 0 1 = .fresh := by decide

/-- Illustrative context program prices count first construction, per-view
binding, two current-argument uses per revision, and optional collector excess. -/
def contextPrices : TemplateCosts := ⟨20,3,12⟩

/-- A cold factory cannot amortize this setup; shared steady revisions can, while
many calls with expensive extra argument checks or GC can reverse that choice. -/
theorem context_preparation_modes :
    ((⟨1,2,0⟩ : ContextPreparationBudget).prices contextPrices 1 10).choose 1 = .fresh ∧
    ((⟨32,64,0⟩ : ContextPreparationBudget).prices contextPrices 1 10).choose 32 = .shared ∧
    ((⟨32,6400,0⟩ : ContextPreparationBudget).prices contextPrices 1 10).choose 32 = .fresh ∧
    ((⟨32,64,100⟩ : ContextPreparationBudget).prices contextPrices 1 10).choose 32 = .fresh := by decide

#print axioms ContextPreparationBudget.selected_bound
#print axioms ContextPreparationBudget.sharing_covered
#print axioms context_preparation_modes
#print axioms contextPreflight_equivalent
#print axioms contextPreflight_revoked
#print axioms ShapePreparationBudget.preparation_covered
#print axioms ShapePreparationBudget.selected_bound
#print axioms Object.PreparedMultimethod.prepareShape_probes
#print axioms shape_preparation_modes
#print axioms Object.PreparedMultimethod.prepareShape_call_correct
#print axioms Object.PreparedMultimethod.prepareShape_preserves
#print axioms Object.PreparedMultimethod.prepareShape_definition
#print axioms Object.PreparedMultimethod.prepareShape_recent
#print axioms Object.NestedMultimethod.call_retains
#print axioms Object.PreparedMultimethod.call_correct
#print axioms Object.PreparedMultimethod.call_preserves
#print axioms Object.NestedMultimethod.call_success
#print axioms Object.NestedMultimethod.call_child_failure
#print axioms Object.NestedMultimethod.callChecked_admitted
#print axioms Object.NestedMultimethod.callChecked_refused
#print axioms EffectiveCosts.workflow_bound
#print axioms EffectiveCosts.cold
#print axioms EffectiveCosts.selected_workflow_bound
#print axioms cold_publication_mode
#print axioms effective_modes
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
/-- Reusable Simula service retains automatic inner ordering under compilation,
including repeated current arguments and rejection before any suffix. -/
def compiledContextRequest (view : View) (units : Int) :=
  Object.MethodCombination.compileSimula contextPreflight (units, view)

/-- Compiled code checks the same CURRENT view and yields identical state/error
traces as the captured-view reference, for every input, not only examples. -/
theorem compiledContext_equivalent (view : View) (units : Int) :
    compiledContextRequest view units =
      Object.MethodCombination.simulaEffective (preflight view) units := by
  rw [compiledContextRequest, Object.MethodCombination.compileSimula_correct,
    contextPreflight_equivalent]

/- The same immutable compiled function receives distinct revisions, including
revoked release and a capacity refusal. No result or old argument is retained. -/
#guard match compiledContextRequest ⟨20,"invoice:2",true⟩ 15 [] with
  | .ok _ trace => trace == ["positive","capacity","invoice","release"]
  | _ => false
#guard match compiledContextRequest ⟨10,"invoice:1",true⟩ 15 [] with
  | .error "refused" trace => trace == ["positive","capacity"]
  | _ => false
#guard match compiledContextRequest ⟨20,"invoice:3",false⟩ 2 [] with
  | .error "refused" trace => trace == ["positive","capacity","invoice","release"]
  | _ => false
#print axioms Object.MethodCombination.compileSimula_correct
#print axioms compiledContext_equivalent
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
open Functional.ContractFamily.PreparationCosts
/-- Illustrative supplied operation prices charge the complete wrapper setup;
these are not Scheme timings and never cross the native checkout boundary. -/
def simulaFactoryPrices : SimulaFactoryCosts := ⟨20,12,3,10,2,8,3,10⟩
/-- One cold factory keeps reference; repeated calls or bindings amortize setup.
Excess GC can reverse the decision even on the same application horizon. -/
theorem simula_factory_modes :
    (⟨1,1,2,0⟩ : SimulaFactoryBudget).choose simulaFactoryPrices = .fresh ∧
    (⟨1,32,2,0⟩ : SimulaFactoryBudget).choose simulaFactoryPrices = .shared ∧
    (⟨1,1,2,0⟩ : SimulaFactoryBudget).choose {simulaFactoryPrices with wrapperSetup := 0} = .shared ∧
    (⟨32,32,2,0⟩ : SimulaFactoryBudget).choose simulaFactoryPrices = .shared ∧
    (⟨32,32,2,100⟩ : SimulaFactoryBudget).choose simulaFactoryPrices = .fresh := by decide
#print axioms SimulaFactoryBudget.selected_bound
#print axioms SimulaFactoryBudget.compilation_covered
#print axioms simula_factory_modes
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
open Object.MethodCombination
/-- The native staged Model uses the captured view initially and the compiled
shared definition after a changed revision. Warm calls never run a selector. -/
def stagedPreflight (revised : Bool) (view : View) (units : Int) :=
  if revised then compileSimula contextPreflight (units, view)
  else simulaEffective (preflight view) units

/-- Both lifecycle representations check the actual current view and preserve
all success/error traces, so switching on revision adds no semantic assumption. -/
theorem stagedPreflight_equivalent (revised : Bool) (view : View) (units : Int) :
    stagedPreflight revised view units = simulaEffective (preflight view) units := by
  cases revised with
  | false => rfl
  | true => exact compiledContext_equivalent view units

/-- An arbitrary multi-revision request stream retains each request's current
argument and view. This compares computations, not only successful results. -/
theorem stagedPreflight_stream (requests : List (Bool × View × Int)) :
    requests.map (fun request => stagedPreflight request.1 request.2.1 request.2.2) =
      requests.map (fun request => simulaEffective (preflight request.2.1) request.2.2) := by
  apply List.map_congr_left
  intro request _
  exact stagedPreflight_equivalent request.1 request.2.1 request.2.2
#print axioms stagedPreflight_equivalent
#print axioms stagedPreflight_stream
end LeanPoo.Examples.AlignedServices

#print axioms LeanPoo.Functional.ContractFamily.PreparationCosts.ContextPreparationBudget.staged_bound

namespace LeanPoo.Examples.AlignedServices
open Object.MethodCombination
/-- The bound unary child checks the reconstructed immutable view on every
method step while accepting fresh units through its ordinary typed signature. -/
def boundPreflight (view : View) := bindSimula contextPreflight view

/-- Moving context validation/binding to reconstruction preserves all Simula
results and failure traces at the current immutable view. Native Type validation
and projection immutability are separate premises, enforced by the constructor. -/
theorem boundPreflight_equivalent (view : View) (units : Int) :
    boundPreflight view units = simulaEffective (preflight view) units := by
  rw [boundPreflight, bindSimula_correct, contextPreflight_equivalent]

/-- Even a successful earlier request cannot authorize a later failing argument
or a new revoked view. Computation equality retains prefix/suffix state traces. -/
theorem boundPreflight_revoked (view : View) (units : Int) (trace : List String)
    (revoked : view.released = false) (positive : 0 < units) (fits : units ≤ view.capacity) :
    boundPreflight view units trace =
      .error "refused" (trace ++ ["positive","capacity","invoice","release"]) := by
  rw [boundPreflight_equivalent]
  exact preflight_revoked view units trace revoked positive fits

/- Three successive independent contexts include a capacity failure and revocation;
each child retains its own bound view rather than the latest successful result. -/
#guard match boundPreflight ⟨20,"invoice:2",true⟩ 15 [] with
  | .ok _ trace => trace == ["positive","capacity","invoice","release"]
  | _ => false
#guard match boundPreflight ⟨10,"invoice:1",true⟩ 15 [] with
  | .error "refused" trace => trace == ["positive","capacity"]
  | _ => false
#guard match boundPreflight ⟨30,"invoice:3",false⟩ 25 [] with
  | .error "refused" trace => trace == ["positive","capacity","invoice","release"]
  | _ => false
#print axioms Object.MethodCombination.bindSimula_correct
#print axioms boundPreflight_equivalent
#print axioms boundPreflight_revoked
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
open Functional.ContractFamily.PreparationCosts
/-- Illustrative operation prices keep per-view binding and setup visible. -/
def simulaBindingPrices : SimulaBindingCosts := ⟨10,10,8,5,2,20⟩
/-- A call-heavy current view amortizes binding; frequent reconstruction and GC
can reverse the choice. Native benchmarks supply their own independent evidence. -/
theorem simula_binding_modes :
    (⟨1,1,0⟩ : SimulaBindingBudget).choose simulaBindingPrices = .fresh ∧
    (⟨1,32,0⟩ : SimulaBindingBudget).choose simulaBindingPrices = .shared ∧
    (⟨32,32,0⟩ : SimulaBindingBudget).choose simulaBindingPrices = .fresh ∧
    (⟨1,32,10⟩ : SimulaBindingBudget).choose simulaBindingPrices = .fresh := by decide
#print axioms SimulaBindingBudget.selected_bound
#print axioms SimulaBindingBudget.binding_covered
#print axioms SimulaBindingBudget.tables_covered
#print axioms Functional.GenericFamily.Partial.emptyWithCapacity_lookup
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.AlignedServices
open Object Object.MethodCombination
/-- One immutable sparse program returns context-parameterized computations;
method installation and unconditional shape preparation precede any binding. -/
def preparedContextProgram :=
  let seed := PreparedMultimethod.create 1 (fun (_ : Int) => [["Reserve", "Object"]])
    (fun (methods : Array (SimulaBody (Int × View) (EStateM String (List String)))) =>
      fun view units => bindSimula methods.toList view units)
    (fun effective units view => effective view units)
  let defined := contextPreflight.reverse.foldl (fun current body =>
    (current.contribute [.any] body).toOption.getD current) seed
  defined.prepareShape [["Reserve", "Object"]]

/-- Bind a new typed view without reinstalling methods or discarding prepared code. -/
def preparedContextRequest (view : View) (units : Int) : Except String (List String) := do
  let program ← preparedContextProgram.mapError (fun _ => "prepare")
  let owner : PreparedContextMultimethod Int _ _ View _ := ⟨program, ⟨0,"",false⟩⟩
  let (action, _) ← ((owner.bindContext view).call units).mapError (fun _ => "dispatch")
  match action [] with
  | .ok _ trace => .ok trace
  | .error error _ => .error error

/- Reuse one compiled program with successively changed actual contexts. -/
#guard (preparedContextRequest ⟨20,"invoice:2",true⟩ 15).toOption ==
  some ["positive","capacity","invoice","release"]
#guard match preparedContextRequest ⟨10,"invoice:1",true⟩ 15 with
  | .error "refused" => true
  | _ => false
#guard match preparedContextRequest ⟨30,"invoice:3",false⟩ 25 with
  | .error "refused" => true
  | _ => false
#print axioms PreparedContextMultimethod.bindContext_program
#print axioms PreparedContextMultimethod.bindContext_sound
#print axioms PreparedContextMultimethod.call_correct
#print axioms PreparedContextMultimethod.call_retains
end LeanPoo.Examples.AlignedServices

#print axioms LeanPoo.Object.PreparedContextMultimethod.call_context
#print axioms LeanPoo.Object.NestedMultimethod.callChecked_context_change

#print axioms LeanPoo.Functional.GenericFamily.rebuiltLookup_reference
#print axioms LeanPoo.Functional.GenericFamily.rebuiltLookup_certified


namespace LeanPoo.Examples.AlignedServices
open Functional
/-- Reconstruct real heterogeneous reserve/cancel/quote services through independent
empty storage. Duplicate reserve is installed once; calls use the reconstructed view. -/
def emptyStorageServices (capacity : Nat) (policy : ServiceBundle.Policy) := do
  let view : ConstructionWorkflow.Interface := ⟨"storage", fun name =>
    if name == "total" then some (.ok 40) else if name == "invoice" then some (.ok 12) else none⟩
  let family ← ((GenericFamily.Partial.emptyWithCapacity ServiceBundle.model.generics policy view capacity).rebuild
    ServiceBundle.model.generics policy view [.reserve,.reserve,.cancel,.quote]).mapError (fun _ => "construction")
  let (reserve, _) ← (family.table.call .reserve 15).mapError (fun _ => "reserve dispatch")
  let (cancel, _) ← (family.table.call .cancel ("customer",true)).mapError (fun _ => "cancel dispatch")
  return (reserve, cancel)

#guard match emptyStorageServices 0 {} with
  | .ok (.ok (remaining,allowed),.ok events) => remaining == 25 && allowed && events == ["customer","invoice:12"]
  | _ => false
#guard match emptyStorageServices 64 {reserveShift := 10, cancelShift := 5} with
  | .ok (.ok (remaining,allowed),.ok events) => remaining == 35 && allowed && events == ["customer","invoice:17"]
  | _ => false
#guard match emptyStorageServices 64 {forbiddenCancel := true} with
  | .error "construction" => true
  | _ => false

/-- Example prices expose fixed interface setup and extra collections explicitly;
small or GC-heavy horizons must not be admitted from table-byte savings alone. -/
def emptyStoragePrices : ContractFamily.PreparationCosts.EmptyStorageCosts := ⟨12,4,2,2,20,30⟩
#guard emptyStoragePrices.interfaceSetup + 1 * emptyStoragePrices.emptyFactory >
  1 * emptyStoragePrices.keyword + emptyStoragePrices.staging + emptyStoragePrices.pruning
#guard emptyStoragePrices.interfaceSetup + 8 * emptyStoragePrices.emptyFactory ≤
  8 * emptyStoragePrices.keyword + emptyStoragePrices.staging + emptyStoragePrices.pruning
#guard emptyStoragePrices.interfaceSetup + 8 * emptyStoragePrices.emptyFactory + 3 * emptyStoragePrices.collection >
  8 * emptyStoragePrices.keyword + emptyStoragePrices.staging + emptyStoragePrices.pruning
#print axioms GenericFamily.Partial.build_lookup_eq
#print axioms GenericFamily.Partial.rebuild_lookup_eq
#print axioms GenericFamily.Partial.rebuild_empty_reference
#print axioms ContractFamily.PreparationCosts.EmptyStorageCosts.covered
end LeanPoo.Examples.AlignedServices


namespace LeanPoo.Examples.AlignedServices
open Functional Prototype.Recursive
/-- Execute the existing shared attestation rather than accepting an external
Boolean seed. Four duplicated child requests become genuine memo hits. -/
def recursiveAttestationCheck : Bool :=
  match Cached.runCertified CyclicAccess.attestation (4,"active") 200 with
  | .error _ => false
  | .ok (receipt,memo) => receipt.result == .value true && memo.entries.length == 5 &&
      memo.statistics.misses == 5 && memo.statistics.hits == 4 &&
      match Cached.runCertified CyclicAccess.attestation (4,"active") 1 memo with
      | .error _ => false
      | .ok (next,after) => next.result == .value true && after.statistics.hits == 5 &&
          after.statistics.steps == memo.statistics.steps
#guard recursiveAttestationCheck
/-- Revocation is a completed false proof, not exhaustion or a cycle diagnostic. -/
def recursiveRevocationCheck : Bool :=
  match CyclicAccess.start CyclicAccess.attestation (4,"revoked") 200 {} {} with
  | .error _ => false
  | .ok version => !version.enabled && !version.closure.snapshot.candidate.interface.release
#guard recursiveRevocationCheck
/-- Supplied example prices: a raw hit still pays current admission. -/
def recursiveMemoPrices : ContractFamily.PreparationCosts.RecursiveMemoCosts := ⟨20,3,30,7,50⟩
#guard recursiveMemoPrices.setup + 1 * recursiveMemoPrices.hit > 1 * recursiveMemoPrices.fresh
#guard recursiveMemoPrices.setup + 8 * recursiveMemoPrices.hit ≤ 8 * recursiveMemoPrices.fresh
#guard recursiveMemoPrices.setup + 8 * recursiveMemoPrices.hit + 3 * recursiveMemoPrices.collection >
  8 * recursiveMemoPrices.fresh
#print axioms Cached.runCertified_hit
#print axioms Cached.runCertified_zero
#print axioms RecursiveSession.call_warm_current
#print axioms ContractFamily.PreparationCosts.RecursiveMemoCosts.covered
end LeanPoo.Examples.AlignedServices

namespace LeanPoo.Examples.GeneralizedHooks
open Prototype Prototype.Generalized
/-- A triangular checkout: price observes final rebate, rebate resets to three;
the second raw field models an audit frame untouched by either hook. -/
def checkout : Protocol (Nat × Nat × String) (Nat × Nat) Bool where
  cook := fun raw => (raw.1, raw.2.1)
  compile := fun price self parent =>
    if price then (30 + self.get.2, parent.get.2)
    else (parent.get.1, 3, parent.get.2.2)
/-- Finite depth one sees the seed rebate; depth two sees the final shared rebate. -/
example : checkout.approximate [true, false] (0, 0, "audit") (0, 0, "seed") 1 =
    (30, 3, "audit") := rfl
/-- Two-stage dependency and the unchanged audit frame have concrete kernel checks. -/
example : checkout.approximate [true, false] (0, 0, "audit") (0, 0, "seed") 2 =
    (33, 3, "audit") := rfl
/-- The prepared snapshot computes exactly the same finite two-stage construction. -/
example : FiniteFix.iterate (checkout.prepareHooks [true, false]).step
    (0, 0, "audit") (0, 0, "seed") 2 = (33, 3, "audit") := rfl
#print axioms Prototype.Generalized.PreparedHooks.step_eq
#print axioms Prototype.Generalized.PreparedHooks.iterate_eq
#print axioms Prototype.Generalized.Protocol.approximate_reindexSelf
end LeanPoo.Examples.GeneralizedHooks
#print axioms LeanPoo.Prototype.Generalized.HookCosts.shared_le_repeated

namespace LeanPoo.Examples.GeneralizedHooks
open Prototype Prototype.Generalized
/-- Service-level focus preserves metadata while updating the nested checkout. -/
def serviceFocus : MonoLens ((Nat × Nat × String) × String) (Nat × Nat × String) :=
  MonoLens.ofGetSet Prod.fst (fun value old => (value, old.2))
/-- Checkout-local price focus preserves rebate and inner audit. -/
def priceFocus : MonoLens (Nat × Nat × String) Nat :=
  MonoLens.ofGetSet Prod.fst (fun value old => (value, old.2))
/-- Checkout-local rebate focus preserves price and inner audit. -/
def rebateFocus : MonoLens (Nat × Nat × String) Nat :=
  MonoLens.ofGetSet (fun raw => raw.2.1) (fun value old => (old.1, value, old.2.2))
/-- Nested focus uses the existing skew-lens composition (outer carrier, inner method). -/
def serviceRebate := serviceFocus.compose rebateFocus
/-- Persistent nested updates retain both distinct audit frames. -/
example : MonoLens.modify serviceRebate (· + 1) ((30, 3, "audit"), "billing") =
    ((30, 4, "audit"), "billing") := rfl
/-- Dependent service construction reads the same cooked rebate three times; the
lens compilers preserve both audits across finite stages. -/
def nestedCheckout : Protocol ((Nat × Nat × String) × String) ((Nat × Nat) × String) Bool where
  cook := fun raw => ((raw.1.1, raw.1.2.1), raw.2)
  compile := fun price => if price then
    lensCompiler (serviceFocus.compose priceFocus)
      (fun (_ : Unit) self _ => 30 + self.get.1.2 + self.get.1.2 + self.get.1.2) ()
    else lensCompiler serviceRebate (fun (_ : Unit) _ _ => 3) ()
/-- Native nested-report's 39/3/billing has a matching finite typed construction. -/
example : nestedCheckout.approximate [true, false] ((0, 0, "audit"), "billing")
    ((0, 0, "seed"), "seed-service") 2 = ((39, 3, "audit"), "billing") := rfl
/-- One compiled binder accepts different seeds, rather than reusing their answers. -/
example : (checkout.prepareHooks [true, false]).bindObserver (0, 0, "audit") 1 (0, 7, "seed") =
    (37, 3) := rfl
#print axioms PreparedHooks.bindObserver_eq
#print axioms Protocol.stepShared_eq
#print axioms Protocol.observe_withCook
#print axioms ObservationWork.cost_mono
end LeanPoo.Examples.GeneralizedHooks

namespace LeanPoo.Examples.GeneralizedHooks
open Prototype Prototype.Generalized
/-- Pair storage gives concrete get-put/put-get/put-put laws, independent of any
Scheme object identity, slot cache or inheritance ancestry representation. -/
theorem serviceFocusLaws : FocusLaws (fun raw : (Nat × Nat × String) × String => raw.1)
    (fun value raw => (value, raw.2)) where
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl
/-- Local billing captures three final-self rebate demands, with unchanged audit. -/
def localBilling : Protocol (Nat × Nat × String) (Nat × Nat) Bool where
  cook := fun raw => (raw.1, raw.2.1)
  compile := fun price self parent => if price then
    (30 + self.get.2 + self.get.2 + self.get.2, parent.get.2)
    else (parent.get.1, 3, parent.get.2.2)
/-- Fused local assembly retains surrounding service metadata in every observation. -/
def focusedBilling := localBilling.prepareFocused
  (fun raw : (Nat × Nat × String) × String => raw.1) (fun value raw => (value, raw.2))
  serviceFocusLaws Prod.fst (fun raw => ((raw.1.1, raw.1.2.1), raw.2)) [true, false]
/-- One focused raw write per stage computes the same 39/3/billing interface. -/
example : focusedBilling.bindObserver ((0, 0, "audit"), "billing") 2
    ((0, 0, "seed"), "different-seed") = ((39, 3), "billing") := rfl
/-- An independently revised metadata frame remains current; no old view is reused. -/
example : focusedBilling.bindObserver ((0, 0, "audit"), "revised-billing") 2
    ((0, 0, "seed"), "old") = ((39, 3), "revised-billing") := rfl
/-- The logical four-fragment/two-stage write count drops from eight to two;
this is an operation model, not a claim about native bytes or collection time. -/
example : focusedWrites 4 2 = 2 ∧ 2 * 4 = 8 := by decide
#print axioms focusDelayed_compose
#print axioms focusDelayed_assemble
#print axioms Protocol.prepareFocused_observe
#print axioms focusedWrites_le
end LeanPoo.Examples.GeneralizedHooks

#print axioms LeanPoo.Prototype.Generalized.focusDelayed_lensGen

namespace LeanPoo.Examples.GeneralizedHooks
open Prototype Prototype.Generalized
/-- Envelope metadata is independent of the local checkout carrier; the native
example represents these same observations through two nested POO slot lenses. -/
theorem envelopeFocusLaws : FocusLaws
    (fun raw : (Nat × Nat × String) × (Bool × String × String) => raw.1)
    (fun value raw => (value, raw.2)) where
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl
/-- Aggregate the two inherited rebate-dependent contributions (three plus two).
This abstracts method grouping, not native call/allocation counts. -/
def localEnvelope : Protocol (Nat × Nat × String) (Nat × Nat) Bool where
  cook := fun raw => (raw.1, raw.2.1)
  compile := fun price self parent => if price then
    (30 + 5 * self.get.2, parent.get.2) else (parent.get.1, 3, parent.get.2.2)
/-- The entire local program is focused into current approval/tenant/service context. -/
def focusedEnvelope := localEnvelope.prepareFocused
  (fun raw : (Nat × Nat × String) × (Bool × String × String) => raw.1)
  (fun value raw => (value, raw.2)) envelopeFocusLaws Prod.fst
  (fun raw => ((raw.1.1, raw.1.2.1), raw.2)) [true, false]
/-- Current approval controls the observable result; the old seed's metadata is
not an admission. This models result/error observations, not host effect timing. -/
def envelopeResult (view : (Nat × Nat) × (Bool × String × String)) :
    Except String (Nat × Nat × String × String × Bool) :=
  if view.2.1 then .ok (view.1.1, view.1.2, view.2.2.2, view.2.2.1, true)
    else .error "billing approval refused"
/-- A current tenant revision is reflected in the successful public result. -/
example : envelopeResult (focusedEnvelope.bindObserver ((0, 0, "audit"), true, "us", "billing") 2
    ((0, 0, "seed"), true, "eu", "billing")) = .ok (45, 3, "billing", "us", true) := rfl
/-- A stale approved seed cannot override the current refused context. -/
example : envelopeResult (focusedEnvelope.bindObserver ((0, 0, "audit"), false, "us", "billing") 2
    ((0, 0, "seed"), true, "eu", "billing")) = .error "billing approval refused" := rfl
end LeanPoo.Examples.GeneralizedHooks
