import LeanPoo.Object.Definition

/-! An outer object inherits a slot containing an inner object. Its extension
applies an independent override to that inner object with Gerbil's `.+`
topology. Lean keeps composition failure in the slot's `Except` value. -/

namespace LeanPoo.Examples.NestedObjectDefinition

inductive InnerKey where
  | x
  | z
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev InnerValue (_ : InnerKey) := Nat

inductive OuterKey where
  | component
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev OuterValue (_ : OuterKey) :=
  Except Object.PlusWithError (Object.Memoized InnerKey InnerValue)

def run : Except String (Option Nat × Option Nat) := do
  let innerBase ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "InnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun _ => "invalid inner base")
  let innerOverride ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "InnerOverride" do
    Object.Declaration.Builder.value .x 2).mapError
      (fun _ => "invalid inner override")
  let outerBase ← (Object.define (Key := OuterKey) (Value := OuterValue)
      "OuterBase" do
    Object.Declaration.Builder.value .component (.ok innerBase)).mapError
      (fun _ => "invalid outer base")
  let outerExtension ← (outerBase.extendWith "OuterExtension" do
    Object.Declaration.Builder.slot .component
      (.computed fun _ inherited =>
        (inherited ()).map fun result =>
          result.bind fun inner => inner.plusWith innerOverride "InnerCombined"))
    |>.mapError (fun _ => "invalid outer extension")
  let result ← (outerExtension.ref .component).mapError
    (fun _ => "missing inner object")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return (inner.read .x, inner.read .z)

#eval run

end LeanPoo.Examples.NestedObjectDefinition
