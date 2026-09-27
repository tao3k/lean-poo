import LeanPoo.Object.Class
import LeanPoo.Object.Memo

namespace LeanPoo.Tests.ClassInstanceMethods

structure Rectangle where
  width : Nat
  height : Nat
  scale : Nat

inductive Key where
  | area
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Value : Key → Type
  | .area => Rectangle → Nat

def base : Object.ClassSpec Key Value :=
  { name := "Rectangle"
    rules := [{ key := .area
                compute := some (Prototype.SlotSpec.baseInstanceMethod
                  (fun rectangle => rectangle.width * rectangle.height)) }] }

def scaled : Object.ClassSpec Key Value :=
  { name := "ScaledShape"
    rules := [{ key := .area
                compute := some (Prototype.SlotSpec.instanceMethod
                  (fun next rectangle => rectangle.scale * (next rectangle).getD 0)) }] }

def audited : Object.ClassSpec Key Value :=
  { name := "AuditedShape"
    rules := [{ key := .area
                compute := some (Prototype.SlotSpec.instanceMethod
                  (fun next rectangle => (next rectangle).getD 0 + 1)) }] }

/-- The receiver is built after all class contributions; C4 installs the
single inherited base behind both mixins. -/
def diamond : Except C4.Error (List String × Option Nat) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Rectangle" [] base.toDeclaration
  let left ← LeanPoo.extend basePlan.schema "ScaledShape" "Rectangle"
    scaled.toDeclaration
  let right ← LeanPoo.extend left.schema "AuditedShape" "Rectangle"
    audited.toDeclaration
  let joined ← LeanPoo.mix right.schema "Final" ["ScaledShape", "AuditedShape"]
    Object.Declaration.empty
  let receiver : Rectangle := ⟨3, 4, 2⟩
  return (joined.precedence, (joined.memoize.read .area).map (· receiver))

#guard match diamond with
  | .ok (order, some result) =>
    order == ["Final", "ScaledShape", "AuditedShape", "Rectangle"] &&
      result == 26
  | _ => false

end LeanPoo.Tests.ClassInstanceMethods
