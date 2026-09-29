import LeanPoo.Object.Definition

namespace LeanPoo.Tests.StrictObjectDefinition

inductive Key where
  | source
  | derived
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value (_ : Key) := Nat

private def checkedInheritance : Except (Object.DefinitionError Key)
    (Option Nat × Option Nat) := do
  let root ← Object.defineStrict (Key := Key) (Value := Value) "Root" do
    Object.Declaration.StrictBuilder.value .source 3
    Object.Declaration.StrictBuilder.default .derived 2
    Object.Declaration.StrictBuilder.slot .derived
      (.computed fun self inherited =>
        some ((inherited ()).getD 0 + (self .source).getD 0))
  let child ← root.extendStrict "Child" do
    Object.Declaration.StrictBuilder.value .source 9
  return (root.read .derived, child.read .derived)

#guard match checkedInheritance with
  | .ok (some 5, some 11) => true
  | _ => false

private def duplicateSlot : Bool :=
  match Object.defineStrict (Key := Key) (Value := Value) "Repeated" (do
      Object.Declaration.StrictBuilder.value .source 1
      Object.Declaration.StrictBuilder.value .source 2) with
  | .error (.duplicate (.slot .source)) => true
  | _ => false

private def duplicateDefault : Bool :=
  match Object.defineStrict (Key := Key) (Value := Value) "Repeated" (do
      Object.Declaration.StrictBuilder.default .source 1
      Object.Declaration.StrictBuilder.default .source 2) with
  | .error (.duplicate (.default .source)) => true
  | _ => false

private def orderedBuilderStillReplaces : Except C4.Error (Option Nat) := do
  let object ← Object.define (Key := Key) (Value := Value) "Ordered" do
    Object.Declaration.Builder.value .source 1
    Object.Declaration.Builder.value .source 2
  return object.read .source

#guard duplicateSlot && duplicateDefault
#guard match orderedBuilderStillReplaces with
  | .ok (some 2) => true
  | _ => false

private def checkedFamily : Except (Object.DefinitionError Key)
    (List String × Option Nat) := do
  let root ← Object.defineStrict (Key := Key) (Value := Value) "Root" do
    Object.Declaration.StrictBuilder.default .source 1
  let left ← root.defineStrictWith "Left" ["Root"] do
    Object.Declaration.StrictBuilder.modifyInherited .source
      (Option.map (· + 2))
  let right ← left.defineStrictWith "Right" ["Root"] do
    Object.Declaration.StrictBuilder.modifyInherited .source
      (Option.map (· + 3))
  let combined ← right.defineStrictNodeWith
      { name := "Combined", parentOrders := [["Left"], ["Right"]] } do
    pure ()
  return (combined.plan.precedence, combined.read .source)

#guard match checkedFamily with
  | .ok (["Combined", "Left", "Right", "Root"], some 6) => true
  | _ => false

private def checkedIndependent : Except (Object.StrictCombineError Key)
    (List String × Option Nat × Bool) := do
  let base ← (Object.define (Key := Key) (Value := Value) "Base" do
    Object.Declaration.Builder.default .source 1).mapError
      (fun error => .combine (.c4 error))
  let increment ← (Object.define (Key := Key) (Value := Value) "Increment" do
    Object.Declaration.Builder.modifyInherited .source
      (Option.map (· + 4))).mapError
        (fun error => .combine (.c4 error))
  let joined ← base.defineStrictFrom "Joined" [increment] do
    Object.Declaration.StrictBuilder.value .derived 7
  let rejectsDuplicate := match base.defineStrictFrom "Repeated" [increment] (do
      Object.Declaration.StrictBuilder.value .derived 1
      Object.Declaration.StrictBuilder.value .derived 2) with
    | .error (.duplicate (.slot .derived)) => true
    | _ => false
  return (joined.plan.precedence, joined.read .source, rejectsDuplicate)

#guard match checkedIndependent with
  | .ok (["Joined", "Base", "Increment"], some 5, true) => true
  | _ => false

private def bulkDeclaration : Except
    (Object.Declaration.DuplicateError Nat) Bool := do
  let program : Object.Declaration.StrictBuilder Nat (fun _ => Nat) PUnit := do
    for key in [:1024] do
      Object.Declaration.StrictBuilder.value key key
      Object.Declaration.StrictBuilder.default key (key + 1)
  let declaration ← program.build
  return declaration.directKeys ==
      (List.range 1024 ++ List.range 1024) &&
    (declaration.slot 1023).isSome &&
    declaration.default 1023 == some 1024

#guard match bulkDeclaration with
  | .ok true => true
  | _ => false

end LeanPoo.Tests.StrictObjectDefinition
