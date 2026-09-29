import LeanPoo.Object.Definition

namespace LeanPoo.Tests.NestedObjectDefinition

inductive Key where
  | x
  | z
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value (_ : Key) := Nat

private def plusTopology : Except Object.PlusWithError
    (List String × Option Nat × Option Nat × Bool × Bool) := do
  let base ← (Object.define (Key := Key) (Value := Value) "Base" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun error => .composition (.c4 error))
  let parent ← (Object.define (Key := Key) (Value := Value) "Parent" do
    Object.Declaration.Builder.value .z 7).mapError
      (fun error => .composition (.c4 error))
  let override ← (parent.extendWith "Override" do
    Object.Declaration.Builder.value .x 2).mapError
      (fun error => .composition (.c4 error))
  let combined ← base.plan.memoizeCompiled |>.plusWith override "Combined"
  let collision := match base.plusWith base "Repeated" with
    | .error (.schema (.duplicateNode "Base")) => true
    | _ => false
  return (combined.plan.precedence, combined.read .x,
    combined.read .z, combined.mode == .compiled, collision)

#guard match plusTopology with
  | .ok (["Combined", "Parent", "Base"], some 2, some 7,
      true, true) => true
  | _ => false

inductive OuterKey where
  | component
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev OuterValue (_ : OuterKey) :=
  Except Object.PlusWithError (Object.Memoized Key Value)

private def nestedError : Except C4.Error Bool := do
  let inner ← Object.define (Key := Key) (Value := Value) "Inner" do
    Object.Declaration.Builder.value .x 1
  let outer ← Object.define (Key := OuterKey) (Value := OuterValue) "Outer" do
    Object.Declaration.Builder.value .component (.ok inner)
  let revised ← outer.extendWith "Revised" do
    Object.Declaration.Builder.slot .component
      (.computed fun _ inherited =>
        (inherited ()).map fun result =>
          result.bind fun base => base.plusWith inner "Collision")
  return match revised.read .component with
    | some (.error (.schema (.duplicateNode "Inner"))) => true
    | _ => false

#guard match nestedError with
  | .ok true => true
  | _ => false

end LeanPoo.Tests.NestedObjectDefinition
