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
  let sibling ← (child.defineWith "Sibling" ["Base"] do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 10))).mapError (fun _ => "invalid sibling")
  let diamond ← (sibling.defineWith "Diamond"
      ["Child", "Sibling"] do pure ()).mapError
        (fun _ => "invalid diamond")
  let method ← (diamond.ref .apply).mapError (fun _ => "missing method")
  return (root.read .total, child.read .total, diamond.read .total, method 2)

#eval run

/-- Independent prototype values can be direct parents of one new object. -/
def combineIndependent : Except String (List String × Option Nat) := do
  let source ← (Object.define (Key := Key) (Value := Value) "Source" do
    Object.Declaration.Builder.value .base 2).mapError
      (fun _ => "invalid source")
  let increment ← (Object.define (Key := Key) (Value := Value) "Increment" do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 10))).mapError (fun _ => "invalid increment")
  let seed ← (Object.define (Key := Key) (Value := Value) "Seed" do
    Object.Declaration.Builder.default .total 4).mapError
      (fun _ => "invalid seed")
  let composed ← (source.defineFrom "Combined" [increment, seed] do
    pure ()).mapError (fun _ => "invalid composition")
  return (composed.plan.precedence, composed.read .total)

#eval combineIndependent

/-- A full C4 node retains separate local parent orders when one flat list
would lose that authoring structure. -/
def groupedParents : Except String (List String × Option Nat) := do
  let root ← (Object.define (Key := Key) (Value := Value) "Object" do
    Object.Declaration.Builder.default .total 1).mapError
      (fun _ => "invalid root")
  let left ← (root.extendWith "Left" do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 1))).mapError (fun _ => "invalid left")
  let right ← (left.defineWith "Right" ["Object"] do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 2))).mapError (fun _ => "invalid right")
  let appendix ← (right.defineWith "Appendix" ["Object"] do
    Object.Declaration.Builder.modifyInherited .total
      (Option.map (· + 3))).mapError (fun _ => "invalid appendix")
  let grouped ← (appendix.defineNodeWith
      { name := "Grouped", parentOrders := [["Left", "Right"], ["Appendix"]] }
      do pure ()).mapError (fun _ => "invalid parent orders")
  return (grouped.plan.precedence, grouped.read .total)

#eval groupedParents

/-- Opt into duplicate-write diagnostics for an author-facing definition. -/
def checkedDefinition : Except String (Option Nat × Option Nat) := do
  let root ← (Object.defineStrict (Key := Key) (Value := Value) "Checked" do
    Object.Declaration.StrictBuilder.value .base 2
    Object.Declaration.StrictBuilder.default .total 1
    Object.Declaration.StrictBuilder.slot .total
      (.computed fun self inherited =>
        some ((inherited ()).getD 0 + (self .base).getD 0))).mapError
          (fun _ => "invalid checked root")
  let child ← (root.extendStrict "CheckedChild" do
    Object.Declaration.StrictBuilder.value .base 5).mapError
      (fun _ => "invalid checked child")
  return (root.read .total, child.read .total)

#eval checkedDefinition

end LeanPoo.Examples.ObjectDefinition
