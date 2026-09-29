import LeanPoo.Object.Definition

namespace LeanPoo.Tests.ObjectDefinition

inductive Key where
  | source
  | derived
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value (_ : Key) := Nat

private def scenario : Except C4.Error
    (Option Nat × Option Nat × Option Nat × List String × Bool) := do
  let root ← Object.define (Key := Key) (Value := Value) "Root" do
    Object.Declaration.Builder.value .source 3
    Object.Declaration.Builder.default .derived 2
    Object.Declaration.Builder.slot .derived
      (.computed fun self inherited =>
        some ((inherited ()).getD 0 + (self .source).getD 0))
  let child ← root.extendWith "Child" do
    Object.Declaration.Builder.value .source 9
  let sibling ← Object.defineIn child.plan.schema "Sibling" ["Root"] do
    Object.Declaration.Builder.modifyInherited .derived
      (Option.map (· + 10))
  let diamond ← Object.defineIn sibling.plan.schema "Diamond"
      ["Child", "Sibling"] do
    pure ()
  let rejectsDuplicate := match root.extendWith "Root" do
      Object.Declaration.Builder.value .source 11 with
    | .error (.duplicateNode "Root") => true
    | _ => false
  return (root.read .derived, child.read .derived,
    diamond.read .derived, diamond.plan.precedence, rejectsDuplicate)

#guard match scenario with
  | .ok (some 5, some 11, some 21,
      ["Diamond", "Child", "Sibling", "Root"], true) => true
  | _ => false

end LeanPoo.Tests.ObjectDefinition
