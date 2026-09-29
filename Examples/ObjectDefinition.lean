import LeanPoo.Object.Definition

/-! Typed `do` declarations build a root, two children, and a C4 diamond.
The inherited method observes the final object's override. A function-valued
slot is called with ordinary Lean function application. -/

namespace LeanPoo.Examples.ObjectDefinition

inductive Key where
  | base
  | total
  | apply
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .base | .total => Nat
  | .apply => Nat → Nat

def base : Except C4.Error (Object.Memoized Key Value) :=
  Object.define "Base" do
    Object.Declaration.Builder.value .base 2
    Object.Declaration.Builder.default .total 1
    Object.Declaration.Builder.slot .total
      (.computed fun self inherited =>
        some ((inherited ()).getD 0 + (self .base).getD 0))
    Object.Declaration.Builder.slot .apply
      (.self fun self => some (fun input => input + (self .total).getD 0))

def run : Except String (Option Nat × Option Nat × Option Nat × Nat) := do
  let root ← base.mapError (fun _ => "invalid root")
  let child ← (root.extendWith "Child" do
    Object.Declaration.Builder.value .base 5).mapError
      (fun _ => "invalid extension")
  let sibling ← (Object.defineIn child.plan.schema "Sibling" ["Base"] do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 10))).mapError (fun _ => "invalid sibling")
  let diamond ← (Object.defineIn sibling.plan.schema "Diamond"
      ["Child", "Sibling"] do pure ()).mapError
        (fun _ => "invalid diamond")
  let method ← (diamond.ref .apply).mapError (fun _ => "missing method")
  return (root.read .total, child.read .total, diamond.read .total, method 2)

#eval run

end LeanPoo.Examples.ObjectDefinition
