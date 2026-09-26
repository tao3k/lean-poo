import LeanPoo.Prototype.Computation

namespace LeanPoo.Examples.PrototypeCore

open LeanPoo.Prototype

/-- The final self is available to every prototype in the chain. -/
def base : FixedFunction Nat Nat := FixedFunction.ofFun fun _ => 1

def setZero : Proto (FixedFunction Nat Nat)
    (FixedFunction Nat Nat) (FixedFunction Nat Nat) :=
  fun _ inherited => FixedFunction.ofFun fun key =>
    if key == 0 then 3 else inherited key

def doubleZero : Proto (FixedFunction Nat Nat)
    (FixedFunction Nat Nat) (FixedFunction Nat Nat) :=
  fun _ inherited => FixedFunction.ofFun fun key =>
    if key == 0 then 2 * inherited key else inherited key

unsafe def mixed : FixedFunction Nat Nat :=
  instantiate (compose doubleZero setZero) base

unsafe def generated : FixedFunction Nat Nat :=
  Generator.instantiate
    (Generator.applyProto doubleZero (Generator.ofProto setZero base))

unsafe def delayedValue : Nat :=
  let constant : DelayedProto Nat Nat Nat := fun _ _ => 3
  let doubled : DelayedProto Nat Nat Nat := fun _ inherited => 2 * inherited.get
  (DelayedProto.instantiate (DelayedProto.compose doubled constant)
    (Thunk.pure 0)).get

/-- Lean checks the Bool intermediate between two delayed prototypes. -/
unsafe def typedDelayedValue : Nat :=
  let parent : DelayedProto Nat Nat Bool :=
    fun _ inherited => inherited.get > 0
  let child : DelayedProto Nat Bool Nat :=
    fun _ inherited => if inherited.get then 7 else 0
  let chain : DelayedProto.Chain Nat Nat Nat :=
    .cons child (.cons parent .nil)
  (chain.instantiate (Thunk.pure 1)).get

#eval (mixed 0, mixed 1)
#eval (generated 0, generated 1)
#eval delayedValue
#eval typedDelayedValue

end LeanPoo.Examples.PrototypeCore
