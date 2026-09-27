import LeanPoo.Object.Lens
import LeanPoo.Object.Builder

namespace LeanPoo.Examples.SpecificationFocus

abbrev Value (_ : String) := Nat

def base : Object.Declaration String Value := Object.Declaration.build do
  Object.Declaration.Builder.value "enabled" 1
  Object.Declaration.Builder.value "retries" 2

def conditional : Prototype.Proto Bool Nat Nat :=
  fun enabled previous => if enabled then previous + 1 else previous

def retryFocus : Prototype.SkewLens Nat Bool Nat
    (Prototype.Next (Option Nat)) (Object.Self String Value) (Option Nat) :=
  { view := fun self => (self "enabled").getD 0 > 0
    update := fun change inherited => Option.map change (inherited ()) }

/-- Only the direct specification of `Child` changes. -/
def addMethod (declaration : Object.Declaration String Value) :
    Object.Declaration String Value :=
  Object.Declaration.buildOn declaration do
    Object.Declaration.Builder.skew "retries" retryFocus conditional

def initial : Except C4.Error (Object.Memoized String Value) := do
  let empty : Object.Schema String Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let child ← LeanPoo.extend basePlan.schema "Child" "Base"
    Object.Declaration.empty
  return child.memoize

def result : Except C4.Error (Option Nat × Option Nat × Bool × Bool) := do
  let original ← initial
  let lens := Object.Lens.specification (Key := String) (Value := Value) "Child"
  let revised ← lens.modify addMethod original
  let direct ← lens.get revised
  return (original.read "retries", revised.read "retries",
    original.plan.precedence == revised.plan.precedence,
    (direct.slot "retries").isSome)

#guard match result with
  | .ok (some 2, some 3, true, true) => true
  | _ => false

#guard match initial with
  | .ok original =>
      match (Object.Lens.specification (Key := String) (Value := Value)
        "Missing").get original with
      | .error (.unknownNode "Missing") => true
      | _ => false
  | _ => false

end LeanPoo.Examples.SpecificationFocus
