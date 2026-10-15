import LeanPoo.Functional.ClosureCosts

/-! Selection is optimal only among the two declared conservative queue bounds.
It does not select minimum measured latency, GC time or global program cost. -/
namespace LeanPoo.Functional.ClosurePolicy
open PositiveEquations IncrementalClosure ClosureCosts

inductive Queue where | append | chunked
  deriving DecidableEq, BEq

def representation : Queue → Representation
  | .append => ⟨true,false,true,true⟩
  | .chunked => ⟨true,true,true,true⟩

def upper (plan : Plan n) (prices : ClosureCosts.Prices) (layout : Layout) (queue : Queue) :=
  charge prices layout (representation queue) n (ceiling plan)

def choose (plan : Plan n) (prices : ClosureCosts.Prices) (layout : Layout) : Queue :=
  if upper plan prices layout .append ≤ upper plan prices layout .chunked then .append else .chunked

theorem choose_minimum (plan : Plan n) (prices : ClosureCosts.Prices) (layout : Layout) (candidate : Queue) :
    upper plan prices layout (choose plan prices layout) ≤ upper plan prices layout candidate := by
  unfold choose
  split <;> cases candidate <;> simp_all [Nat.le_of_lt]

def solve (plan : Plan n) : Queue → Result plan (Vector.replicate n false) (List.ofFn id)
  | .append => fastClose plan
  | .chunked => ChunkedClosure.close plan

theorem solve_stats (plan : Plan n) (queue : Queue) : (solve plan queue).stats = (ChunkedClosure.close plan).stats := by
  cases queue
  · exact (ChunkedClosure.close_stats plan).symm
  · rfl

theorem solve_canonical (plan : Plan n) (queue : Queue) :
    values (solve plan queue).store = (PositiveEquations.close plan.source).value := by
  cases queue
  · exact fast_canonical plan
  · rw [solve,ChunkedClosure.close_store]; exact fast_canonical plan

/-- The selected executed result is within every candidate's declared ceiling.
Primitive/layout prices and exclusive scratch remain explicit premises. -/
theorem selected_bound (plan : Plan n) (prices : ClosureCosts.Prices) (layout : Layout) (candidate : Queue) :
    charge prices layout (representation (choose plan prices layout)) n (solve plan (choose plan prices layout)).stats ≤
      upper plan prices layout candidate := by
  rw [solve_stats]
  exact Nat.le_trans (backend_bound plan prices layout _) (choose_minimum plan prices layout candidate)

/-- Allocation-only specialization used by the Scheme default. Equal bounds
prefer append. This is a least upper bound choice, not a latency prediction. -/
def minimumAllocation (plan : Plan n) : Queue := if plan.edgeCount ≤ n then .append else .chunked

def queueCeiling (plan : Plan n) : Queue → Nat
  | .append => n+plan.edgeCount
  | .chunked => n+n

theorem minimumAllocation_optimal (plan : Plan n) (candidate : Queue) :
    queueCeiling plan (minimumAllocation plan) ≤ queueCeiling plan candidate := by
  unfold minimumAllocation
  split <;> cases candidate <;> simp_all [queueCeiling] <;> omega
end LeanPoo.Functional.ClosurePolicy
