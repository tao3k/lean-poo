import LeanPoo.Object.SharedFamily
import LeanPoo.Object.Definition

namespace LeanPoo.Examples.SharedFamily

abbrev Value (_ : String) := Nat

/-- Two independently extended snapshots retain one explicitly shared
prototype identity when composed inside an inherited component slot. -/
def run : Except String (List String × Option Nat × Option Nat) := do
  let defaults ← (Object.define (Key := String) (Value := Value) "Defaults" do
    Object.Declaration.Builder.value "budget" 1
    Object.Declaration.Builder.value "retries" 5)
    |>.mapError (fun _ => "defaults")
  let shifted ← (defaults.extendWith "Shift" do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· + 10)))
    |>.mapError (fun _ => "shift")
  let scaled ← (defaults.extendWith "Scale" do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· * 2)))
    |>.mapError (fun _ => "scale")
  let outerValue (_ : String) :=
    Except Object.SharedCombineError (Object.Memoized String Value)
  let container ← (Object.define (Key := String) (Value := outerValue) "Container" do
    Object.Declaration.Builder.value "component" (.ok shifted))
    |>.mapError (fun _ => "container")
  let extension ← (container.extendWith "ContainerExtension" do
    Object.Declaration.Builder.slot "component"
      (Object.Nested.mixSharedWith scaled ["Defaults"] "CombinedComponent"))
    |>.mapError (fun _ => "container extension")
  let result ← extension.ref "component" |>.mapError (fun _ => "component")
  let inner ← result |>.mapError (fun _ => "component composition")
  return (inner.plan.precedence, inner.read "budget", inner.read "retries")

#eval run

end LeanPoo.Examples.SharedFamily
