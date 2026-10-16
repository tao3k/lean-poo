import LeanPoo.Object.MultimethodCombination
import LeanPoo.Functional.ContractFamily
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
