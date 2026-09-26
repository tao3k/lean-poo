import LeanPoo.Prototype.Lens

namespace LeanPoo.Examples.LensPrototype

open LeanPoo.Prototype

/-- Change one component of a computation while preserving the other. -/
def addToFirst (amount : Nat) : DelayedProto (Nat × Bool) (Nat × Bool) (Nat × Bool) :=
  lensGen Prod.fst (fun value inherited => (value, inherited.2))
    (fun increment _ inherited => inherited.get + increment) amount

unsafe def result : Nat × Bool :=
  (DelayedProto.instantiate
    (DelayedProto.compose (addToFirst 3) (addToFirst 2))
    (Thunk.pure (4, true))).get

#eval result

end LeanPoo.Examples.LensPrototype
