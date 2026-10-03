import LeanPoo.Object.AncestryTransform
import LeanPoo.Object.Definition
import LeanPoo.Object.Prototype
import LeanPoo.Prototype.Target

namespace LeanPoo.Examples.TargetAndWrapping

abbrev Value (_ : String) := Nat
abbrev Self := Object.Self String Value

/-- Instrument every existing budget contribution, then add a new policy
layer. The new layer participates in inheritance without being instrumented. -/
def wrapComponent : Except String (Option Nat × Option Nat × Option Nat) := do
  let defaults ← (Object.define (Key := String) (Value := Value) "Defaults" do
    Object.Declaration.Builder.value "budget" 1)
    |>.mapError (fun _ => "defaults")
  let add ← (defaults.extendWith "Add" do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· + 10)))
    |>.mapError (fun _ => "add")
  let scale ← (add.defineWith "Scale" ["Defaults"] do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· * 2)))
    |>.mapError (fun _ => "scale")
  let component ← (scale.defineWith "Component" ["Add", "Scale"] do pure ())
    |>.mapError (fun _ => "component")
  let wrapped := component.wrapAncestrySlots fun _ key spec =>
    if key == "budget" then .computed fun self inherited =>
      (spec.eval self inherited).map (· + 1)
    else spec
  let future ← (wrapped.extendWith "Policy" do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· * 3)))
    |>.mapError (fun _ => "policy")
  return (component.read "budget", wrapped.read "budget", future.read "budget")

#eval wrapComponent

private def setX (value : Nat) : Prototype.DelayedProto Self Self Self :=
  fun _ inherited => fun key =>
    if key == "x" then some value else inherited.get key

/-- Observe how retained formulas and constant target specifications behave
when another extension supplies a new x. General first-class extension uses
the existing unsafe fixed-point operation. -/
unsafe def targetPolicies : Except String (List (String × Option Nat × Option Nat)) := do
  let source ← (Object.define (Key := String) (Value := Value) "Computed" do
    Object.Declaration.Builder.value "x" 1
    Object.Declaration.Builder.slot "double"
      (.self fun self => (self "x").map (2 * ·)))
    |>.mapError (fun _ => "source")
  let pair := source.toFirstClassObject
  let change : Self → Self := fun current key =>
    if key == "x" then some 100 else current key
  let edited := pair.updateTargetOutOfSync change
  let frozen := pair.overwriteTargetSpecification change
  let editedChild := edited.extend (setX 7)
  let frozenChild := frozen.extend (setX 7)
  let detached := pair.detachTarget change
  return [("target-only edit", edited.value "x", edited.value "double"),
    ("retained specification extended", editedChild.value "x", editedChild.value "double"),
    ("constant specification extended", frozenChild.value "x", frozenChild.value "double"),
    ("detached target", detached.get "x", detached.get "double")]

#eval targetPolicies

end LeanPoo.Examples.TargetAndWrapping
