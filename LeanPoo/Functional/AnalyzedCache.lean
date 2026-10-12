import LeanPoo.Functional.DependencyAnalysis
import LeanPoo.Functional.ContextSlot

/-! Cache analyzed computed results using the existing certified one-context
slot. Success/error observations and result contracts retain exact body/provider
indices. A rebind needs universal evaluation equality. -/
namespace LeanPoo.Functional.Computation
open Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Result : Context → Type w}
variable {code : Computation Context Key Value Result}
variable {provider : Provider Context Key Value} {Claim : ∀ c, Result c → Prop}

def OutcomeValid (Claim : ∀ c, Result c → Prop) (context : Context)
    (outcome : Except (ComputationError Key) (Result context)) : Prop :=
  match outcome with | .error _ => True | .ok result => Claim context result

private abbrev Stored (_Value : Context → Key → Type w) (Result : Context → Type w) : Context → Unit → Type (max v w) :=
  fun c _ => Except (ComputationError Key) (Result c)

/-- Use one ordinary certified dependency to store the computed observation.
The existing ContextSlot owns all context comparison/build/replacement behavior. -/
def certified (code : Computation Context Key Value Result) (provider : Provider Context Key Value)
    (Claim : ∀ c, Result c → Prop)
    (admit : ∀ c, OutcomeValid Claim c (code.evaluate provider c)) :
    Certified (Value := Stored Value Result) [()]
      (fun c data => OutcomeValid Claim c data.1) :=
  ⟨(fun c => code.evaluate provider c, PUnit.unit), admit⟩

structure Cache (code : Computation Context Key Value Result) (provider : Provider Context Key Value)
    (Claim : ∀ c, Result c → Prop) where
  admitted : ∀ c, OutcomeValid Claim c (code.evaluate provider c)
  slot : ContextSlot (certified code provider Claim admitted)

def Cache.empty (code : Computation Context Key Value Result) (provider : Provider Context Key Value)
    (Claim : ∀ c, Result c → Prop)
    (admit : ∀ c, OutcomeValid Claim c (code.evaluate provider c)) : Cache code provider Claim :=
  ⟨admit, ContextSlot.empty (certified code provider Claim admit)⟩

/-- Results include errors and retain their exact execution equation and success
contract. On a hit, the certified slot returns the retained observation directly. -/
def Cache.read [DecidableEq Context] (cache : Cache code provider Claim) (context : Context) :
    {outcome : Except (ComputationError Key) (Result context) //
      outcome = code.evaluate provider context ∧ OutcomeValid Claim context outcome} ×
      Cache code provider Claim × Bool :=
  let (data, next, reused) := cache.slot.read context
  (⟨data.val.1, congrArg Prod.fst data.property.1, data.property.2⟩,
    {cache with slot := next}, reused)

theorem Cache.read_result [DecidableEq Context] (cache : Cache code provider Claim) (context : Context) :
    (cache.read context).1.val = code.evaluate provider context := (cache.read context).1.property.1

/-- No new body execution or analytic admission runs during proved rebinding.
The existing family cast preserves the entire one-context slot. -/
def Cache.rebind (cache : Cache code provider Claim) (next : Provider Context Key Value)
    (same : ∀ c, code.evaluate provider c = code.evaluate next c) : Cache code next Claim :=
  let admit : ∀ c, OutcomeValid Claim c (code.evaluate next c) := fun c => same c ▸ cache.admitted c
  ⟨admit, cache.slot.rebind (certified code next Claim admit) (by
    apply Prod.ext
    · exact funext same
    · rfl)⟩

private theorem slot_rebind_reused [DecidableEq Context]
    {keys : List Key} {Joint : ∀ c, Results Value c keys → Prop}
    {left : Certified keys Joint} (slot : ContextSlot left) (right : Certified keys Joint)
    (same : left.factories = right.factories) (context : Context) :
    ((slot.rebind right same).read context).2.2 = (slot.read context).2.2 := by
  have equal := Certified.ext left right same
  subst right
  simp [ContextSlot.rebind]

/-- Proved rebinding preserves the exact context-hit decision, as well as data
and its contract. A retained hot result is not recomputed by the migration. -/
theorem Cache.rebind_read_reused [DecidableEq Context] (cache : Cache code provider Claim)
    (next : Provider Context Key Value) (same : ∀ c, code.evaluate provider c = code.evaluate next c)
    (context : Context) :
    ((cache.rebind next same).read context).2.2 = (cache.read context).2.2 := by
  unfold Cache.rebind Cache.read
  dsimp only
  exact slot_rebind_reused _ _ _ context

theorem Cache.rebind_read_result [DecidableEq Context] (cache : Cache code provider Claim)
    (next : Provider Context Key Value) (same : ∀ c, code.evaluate provider c = code.evaluate next c)
    (context : Context) :
    ((cache.rebind next same).read context).1.val = (cache.read context).1.val := by
  rw [Cache.read_result, Cache.read_result, same]

end LeanPoo.Functional.Computation
