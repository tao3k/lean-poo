import LeanPoo.Object.SpecificationComposition
import LeanPoo.Object.Definition
import LeanPoo.Object.Lens

namespace LeanPoo.Tests.SpecificationComposition

abbrev Value (_ : String) := Nat

private def family : Except C4.Error (Object.Memoized String Value) := do
  let seed ← Object.define (Key := String) (Value := Value) "Seed" do
    Object.Declaration.Builder.value "x" 1
    Object.Declaration.Builder.value "z" 5
    Object.Declaration.Builder.default "limit" 3
  let offset ← seed.extendWith "Offset" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 10))
  let scale ← offset.defineWith "Scale" ["Seed"] do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 3))
  let a ← scale.defineWith "A" ["Offset"] do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 2))
    Object.Declaration.Builder.default "limit" 7
  let b ← a.defineWith "B" ["Scale"] do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 4))
    Object.Declaration.Builder.default "limit" 9
  b.defineWith "Future" ["Seed"] do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 5))

/-- The source identities disappear from the derived ancestry, their shared
seed runs once, direct extensions compose in the specified order, and a
future ancestor runs before both finalizers. Defaults keep specificity. -/
private def results : Except String Bool := do
  let original ← family |>.mapError (fun _ => "family")
  let forward ← original.plan.memoizeCompiled.fuseSpecifications "Fused" ["A", "B"]
    |>.mapError (fun _ => "fuse")
  let reverse ← original.plan.memoizeIndexed.fuseSpecifications "Reverse" ["B", "A"]
    |>.mapError (fun _ => "reverse")
  let focus := Object.Lens.prototypeSpecification
    (Key := String) (Value := Value) "Fused"
  let future ← focus.modify (fun spec =>
    { spec with parentOrders := spec.parentOrders ++ [["Future"]] }) forward
    |>.mapError (fun _ => "future")
  let empty ← original.fuseSpecifications "Empty" [] true
    |>.mapError (fun _ => "empty")
  return forward.plan.precedence == ["Fused", "Offset", "Scale", "Seed"] &&
    forward.read "x" == some 34 && forward.read "z" == some 5 &&
    forward.read "limit" == some 7 && forward.mode == .compiled &&
    reverse.plan.precedence == ["Reverse", "Scale", "Offset", "Seed"] &&
    reverse.read "x" == some 70 && reverse.read "limit" == some 9 &&
    reverse.mode == .indexed && future.read "x" == some 64 &&
    future.plan.precedence == ["Fused", "Offset", "Scale", "Future", "Seed"] &&
    original.plan.precedence == ["Future", "Seed"] &&
    original.read "x" == some 6 && forward.read "x" == some 34 &&
    empty.plan.precedence == ["Empty"] && empty.read "x" == none &&
    ((empty.plan.schema.graph.findNode? "Empty").map (·.suffix)) == some true

#guard match results with
  | .ok true => true
  | _ => false

private def failures : Except C4.Error Bool := do
  let original ← family
  let unknown := match original.fuseSpecifications "Unknown" ["Missing"] with
    | .error (.c4 (.unknownNode "Missing")) => true
    | _ => false
  let duplicate := match original.fuseSpecifications "Seed" ["A"] with
    | .error (.c4 (.duplicateNode "Seed")) => true
    | _ => false
  let repeated := match original.fuseSpecifications "Repeated" ["A", "A"] with
    | .error (.repeatedSource "A") => true
    | _ => false
  let appliedTwice := match original.fuseSpecifications "Twice" ["A", "Offset"] with
    | .error (.sourceInAncestry "Offset") => true
    | _ => false
  let left ← original.defineWith "OrderedLeft" ["Offset", "Scale"] do pure ()
  let right ← left.defineWith "OrderedRight" ["Scale", "Offset"] do pure ()
  let conflict := match right.fuseSpecifications "Conflict"
      ["OrderedLeft", "OrderedRight"] with
    | .error (.c4 .inconsistentOrder) => true
    | _ => false
  return unknown && duplicate && repeated && appliedTwice && conflict

#guard match failures with
  | .ok true => true
  | _ => false

/-- A constant finalizer may ignore a failing delayed inherited computation;
composing direct specifications must not force it early. -/
private def delayedOverride : Bool := Id.run do
  let parent : Object.Declaration String Value := Object.Declaration.build do
    Object.Declaration.Builder.slot "x" (.computed fun _ _ => panic! "forced parent")
  let child : Object.Declaration String Value := Object.Declaration.build do
    Object.Declaration.Builder.value "x" 42
  let composed := child.compose parent
  let some method := composed.slot "x" | return false
  return method.eval (fun _ => none) (fun _ => none) == some 42

#guard delayedOverride

/-- Last-write-wins within a direct declaration is normalized before
composition; a repeated key must not apply the final method twice. Both
fragments still receive the final self. -/
private def repeatedDirectKey : Bool := Id.run do
  let child : Object.Declaration String Value :=
    { slots := [⟨"x", .constant (some 999), fun _ => inferInstance⟩,
        ⟨"x", .computed (fun self next =>
          (next ()).map (· + (self "z").getD 0)), fun _ => inferInstance⟩]
      defaults := [] }
  let parent : Object.Declaration String Value := Object.Declaration.build do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 2))
  let composed := child.compose parent
  let some method := composed.slot "x" | return false
  return composed.slots.length == 1 &&
    method.eval (fun key => if key == "z" then some 10 else none)
      (fun _ => some 1) == some 12

#guard repeatedDirectKey

end LeanPoo.Tests.SpecificationComposition
