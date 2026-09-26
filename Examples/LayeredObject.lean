import LeanPoo.Object.Memo
import LeanPoo.Object.Prototype

namespace LeanPoo.Examples.LayeredObject

/-- A small PO object: a base value and an inherited override. -/
def emptySchema : Object.Schema String (fun _ => Nat) :=
  { graph := { nodes := [] }, declaration := fun _ => none }

def base : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withValue "retries" 2

def retryLayer : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "retries"
    (.computed fun _ inherited => some ((inherited ()).getD 0 + 1))

/-- `extend` preserves the inherited computation; `memoize` gives an
executable object whose slot is forced when read. -/
def retries : Except C4.Error (Option Nat) := do
  let basePlan ← LeanPoo.mix emptySchema "Base" [] base
  let layer ← basePlan.memoize |>.extend "RetryLayer" retryLayer
  return layer.read "retries"

/-- The same C4 slot plan can be instantiated as the paper's first-class
instance/prototype pair; the plan remains its sole slot evaluator. -/
unsafe def firstClassRetries : Except C4.Error (Option Nat) := do
  let basePlan ← LeanPoo.mix emptySchema "Base" [] base
  let layer ← LeanPoo.extend basePlan.schema "RetryLayer" "Base" retryLayer
  return layer.toFirstClassObject.value "retries"

/-- The resulting executable object remains a prototype that can be cloned
with a different direct value. -/
def clonedRetries : Except (CloneError String) (Option Nat) := do
  let basePlan ← (LeanPoo.mix emptySchema "Base" [] base).mapError .c4
  let layer ← (basePlan.memoize.extend "RetryLayer" retryLayer).mapError .c4
  let clone ← layer.clone "Cloned" [⟨"retries", 8⟩]
  return clone.read "retries"

/-- Independent prototype families can be mixed after checking node names. -/
def combinedValues : Except Object.CombineError (Option Nat × Option Nat) := do
  let left ← (LeanPoo.mix emptySchema "RetryBase" [] base).mapError .c4
  let timeoutDeclaration : Object.Declaration String (fun _ => Nat) :=
    Object.Declaration.empty |>.withValue "timeout" 10
  let right ← (LeanPoo.mix emptySchema "TimeoutBase" []
    timeoutDeclaration).mapError .c4
  let combined ← left.memoize.mixWith right.memoize "Combined"
    Object.Declaration.empty
  return (combined.read "retries", combined.read "timeout")

/-- Revising a prototype yields a new object and leaves the old instance intact. -/
def revisedValues : Except C4.Error (Option Nat × Option Nat) := do
  let basePlan ← LeanPoo.mix emptySchema "Base" [] base
  let original := basePlan.memoize
  let revised ← original.reviseSlot "Base" "retries" (.constant (some 5))
  return (original.read "retries", revised.read "retries")

/-- Both branches inherit the same base. C4 includes that base once and
orders the inherited method computations consistently. -/
def diamondRetries : Except C4.Error (List String × Option Nat) := do
  let basePlan ← LeanPoo.mix emptySchema "Base" [] base
  let left ← LeanPoo.extend basePlan.schema "Left" "Base" retryLayer
  let rightDeclaration : Object.Declaration String (fun _ => Nat) :=
    Object.Declaration.empty |>.withSlot "retries"
      (.computed fun _ inherited => some ((inherited ()).getD 0 + 10))
  let right ← LeanPoo.extend left.schema "Right" "Base" rightDeclaration
  let diamond ← LeanPoo.mix right.schema "Diamond" ["Left", "Right"]
    Object.Declaration.empty
  return (diamond.precedence, diamond.memoize.read "retries")

#eval retries
#eval firstClassRetries
#eval clonedRetries
#eval combinedValues
#eval revisedValues
#eval diamondRetries

end LeanPoo.Examples.LayeredObject
