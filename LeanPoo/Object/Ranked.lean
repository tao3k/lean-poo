import LeanPoo.Object.Instance

/-!
An explicitly ranked dependency discipline supplies a total fixed point for
open-recursive slots. The locality proof is about resolved values, so a slot
may use inherited methods as long as its self reads have lower rank.
-/

namespace LeanPoo.Object

universe u v

/-- A plan whose result at each key depends on self only at smaller ranks. -/
structure Ranked (Key : Type u) (Value : Key → Type v)
    (plan : Plan Key Value) where
  rank : Key → Nat
  dependsOnLower : ∀ key (left right : Self Key Value),
    (∀ dependency, rank dependency < rank key →
      left dependency = right dependency) →
    plan.resolve key left = plan.resolve key right

private def Ranked.eval {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (ranked : Ranked Key Value plan)
    (key : Key) : Option (Value key) :=
  plan.resolve key (fun dependency =>
    if _smaller : ranked.rank dependency < ranked.rank key then
      ranked.eval dependency
    else none)
termination_by ranked.rank key
decreasing_by exact _smaller

/-- Instantiate an open-recursive plan by well-founded slot evaluation. -/
def Ranked.instantiate {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (ranked : Ranked Key Value plan) :
    Instance Key Value plan :=
  { state := ranked.eval
    agrees := by
      intro key
      have same := ranked.dependsOnLower key ranked.eval
        (fun dependency =>
          if smaller : ranked.rank dependency < ranked.rank key then
            ranked.eval dependency
          else none)
        (by
          intro dependency smaller
          simp [smaller])
      rw [same]
      exact (Ranked.eval.eq_1 ranked key).symm }

end LeanPoo.Object
