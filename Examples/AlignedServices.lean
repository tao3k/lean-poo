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
#print axioms shared_checks
end LeanPoo.Examples.AlignedServices
