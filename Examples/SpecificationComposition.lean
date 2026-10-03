import LeanPoo.Object.Definition
import LeanPoo.Object.SpecificationComposition
import LeanPoo.Object.Lens

namespace LeanPoo.Examples.SpecificationComposition

abbrev Value (_ : String) := Nat

/-- Two component policies contribute independent ancestors and finalizers.
A later infrastructure parent is included before the combined finalizers. -/
def run : Except String (List String × Option Nat × Option Nat) := do
  let defaults ← (Object.define (Key := String) (Value := Value) "Defaults" do
    Object.Declaration.Builder.value "budget" 1)
    |>.mapError (fun _ => "defaults")
  let add ← (defaults.extendWith "Add" do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· + 10)))
    |>.mapError (fun _ => "add")
  let scale ← (add.defineWith "Scale" ["Defaults"] do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· * 3)))
    |>.mapError (fun _ => "scale")
  let policyA ← (scale.defineWith "PolicyA" ["Add"] do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· * 2)))
    |>.mapError (fun _ => "policy A")
  let policyB ← (policyA.defineWith "PolicyB" ["Scale"] do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· + 4)))
    |>.mapError (fun _ => "policy B")
  let family ← (policyB.defineWith "Infrastructure" ["Defaults"] do
    Object.Declaration.Builder.modifyInherited "budget" (Option.map (· + 5)))
    |>.mapError (fun _ => "infrastructure")
  let fused ← family.fuseSpecifications "CombinedPolicy" ["PolicyA", "PolicyB"]
    |>.mapError (fun _ => "combined policy")
  let focus := Object.Lens.prototypeSpecification
    (Key := String) (Value := Value) "CombinedPolicy"
  let revised ← focus.modify (fun spec =>
    { spec with parentOrders := spec.parentOrders ++ [["Infrastructure"]] }) fused
    |>.mapError (fun _ => "revised policy")
  return (revised.plan.precedence, fused.read "budget", revised.read "budget")

#eval run

end LeanPoo.Examples.SpecificationComposition
