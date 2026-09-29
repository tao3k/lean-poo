import LeanPoo.Object.Definition
import LeanPoo.Object.Nested

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
      (Object.Nested.plusWith inner "Collision")
  return match revised.read .component with
    | some (.error (.schema (.duplicateNode "Inner"))) => true
    | _ => false

#guard match nestedError with
  | .ok true => true
  | _ => false

private def nestedDiamond : Except String
    (List String × Option Nat × Option Nat) := do
  let base ← (Object.define (Key := Key) (Value := Value) "InnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun _ => "invalid inner base")
  let addTen ← (Object.define (Key := Key) (Value := Value) "AddTen" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)))
      |>.mapError (fun _ => "invalid left override")
  let double ← (Object.define (Key := Key) (Value := Value) "Double" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)))
      |>.mapError (fun _ => "invalid right override")
  let outer ← (Object.define (Key := OuterKey) (Value := OuterValue)
      "OuterBase" do
    Object.Declaration.Builder.value .component (.ok base)).mapError
      (fun _ => "invalid outer base")
  let left ← (outer.extendWith "Left" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith addTen "InnerLeft"))
      |>.mapError (fun _ => "invalid left")
  let right ← (left.defineWith "Right" ["OuterBase"] do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith double "InnerRight"))
      |>.mapError (fun _ => "invalid right")
  let diamond ← (right.defineWith "Diamond" ["Left", "Right"] do
    pure ()) |>.mapError (fun _ => "invalid diamond")
  let result ← (diamond.ref .component).mapError
    (fun _ => "missing component")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return (diamond.plan.precedence, inner.read .x, inner.read .z)

#guard match nestedDiamond with
  | .ok (["Diamond", "Left", "Right", "OuterBase"], some 12,
      some 5) => true
  | _ => false

abbrev SharedValue (_ : OuterKey) :=
  Except LeanPoo.CompositionError (Object.Memoized Key Value)

private def nestedSharedFamily : Except String (Option Nat) := do
  let base ← (Object.define (Key := Key) (Value := Value) "SharedBase" do
    Object.Declaration.Builder.value .x 1).mapError
      (fun _ => "invalid base")
  let override ← (base.defineWith "SharedOverride" [] do
    Object.Declaration.Builder.value .x 2).mapError
      (fun _ => "invalid override")
  let basePlan ← (Object.compile override.plan.schema "SharedBase").mapError
    (fun _ => "invalid base plan")
  let outer ← (Object.define (Key := OuterKey) (Value := SharedValue)
      "SharedOuter" do
    Object.Declaration.Builder.value .component (.ok basePlan.memoize))
      |>.mapError (fun _ => "invalid outer")
  let extended ← (outer.extendWith "SharedOuterExtension" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plus "InnerCombined" "SharedOverride"))
      |>.mapError (fun _ => "invalid outer extension")
  let result ← (extended.ref .component).mapError
    (fun _ => "missing component")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return inner.read .x

#guard match nestedSharedFamily with
  | .ok (some 2) => true
  | _ => false

end LeanPoo.Tests.NestedObjectDefinition
