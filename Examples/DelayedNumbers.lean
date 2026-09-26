import LeanPoo.Prototype.Computation

namespace LeanPoo.Examples.DelayedNumbers

open LeanPoo.Prototype

/-- The paper's number-thunk increments, expressed with Lean's `Thunk`. -/
def addOne : DelayedProto Nat Nat Nat :=
  fun _ inherited => inherited.get + 1

def double : DelayedProto Nat Nat Nat :=
  fun _ inherited => 2 * inherited.get

unsafe def addAfterDouble : Nat :=
  (DelayedProto.instantiate
    (DelayedProto.compose addOne double) (Thunk.pure 30)).get

unsafe def doubleAfterAdd : Nat :=
  (DelayedProto.instantiate
    (DelayedProto.compose double addOne) (Thunk.pure 30)).get

#eval (addAfterDouble, doubleAfterAdd)

end LeanPoo.Examples.DelayedNumbers
