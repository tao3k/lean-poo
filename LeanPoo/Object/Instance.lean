import LeanPoo.Object.Cache

namespace LeanPoo.Object

universe u v

/-- An object instance is a fixed point of its C4-ordered slot resolver. -/
structure Instance (Key : Type u) (Value : Key → Type v)
    (plan : Plan Key Value) where
  state : Self Key Value
  agrees : ∀ key, plan.resolve key state = state key

theorem Instance.agreesResolve {Key : Type} {Value : Key → Type}
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (key : Key) :
    resolve plan.schema plan.root key instanceValue.state =
      .ok (instanceValue.state key) := by
  rw [resolve_compiled, instanceValue.agrees]

def Instance.ref {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (key : Key) : Except (LookupError Key) (Value key) :=
  plan.ref key instanceValue.state

/-- Assemble selected slots against this instance's validated plan. -/
def Instance.prepare {Key : Type u} {Value : Key → Type v}
    [BEq Key] [Hashable Key] {plan : Plan Key Value}
    (_instanceValue : Instance Key Value plan) (keys : List Key) :
    Prepared Key Value :=
  plan.prepare keys

/-- Start an explicit value cache tied to the final self of this instance. -/
def Instance.cache {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] {plan : Plan Key Value}
    (instanceValue : Instance Key Value plan) (keys : List Key) :
    Cache (instanceValue.prepare keys) instanceValue.state :=
  Cache.empty (instanceValue.prepare keys) instanceValue.state

/-- Cached reads agree with the fixed-point instance, including cache misses. -/
theorem Instance.cachedRead {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (keys : List Key)
    (cache : Cache (instanceValue.prepare keys) instanceValue.state) (key : Key) :
    (cache.read key).1 = instanceValue.state key := by
  rw [cache.read_sound, (instanceValue.prepare keys).resolve_sound]
  exact instanceValue.agrees key

/-- A closed plan computes the same slots regardless of the supplied self. -/
structure Closed (Key : Type u) (Value : Key → Type v)
    (plan : Plan Key Value) where
  independent : ∀ key (left right : Self Key Value),
    plan.resolve key left = plan.resolve key right

/-- Closed plans have a total instance without general recursion. -/
def Closed.instantiate {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (closed : Closed Key Value plan) :
    Instance Key Value plan :=
  let emptySelf : Self Key Value := fun _ => none
  { state := fun key => plan.resolve key emptySelf
    agrees := by
      intro key
      exact closed.independent key (fun key => plan.resolve key emptySelf) emptySelf }

end LeanPoo.Object
