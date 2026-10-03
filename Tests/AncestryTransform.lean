import LeanPoo.Object.AncestryTransform
import LeanPoo.Object.Definition

namespace LeanPoo.Tests.AncestryTransform

abbrev Value (_ : String) := Nat

private def source : Except C4.Error (Object.Memoized String Value) := do
  let seed ← Object.define (Key := String) (Value := Value) "Seed" do
    Object.Declaration.Builder.value "x" 1
    Object.Declaration.Builder.value "z" 5
    Object.Declaration.Builder.default "limit" 7
  let left ← seed.extendWith "Left" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 10))
  let right ← left.defineWith "Right" ["Seed"] do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 2))
  let unused ← right.defineWith "Unused" [] do
    Object.Declaration.Builder.value "x" 99
  unused.defineWith "Diamond" ["Left", "Right"] do pure ()

private def addOne (_name key : String)
    (spec : Object.SlotPayload String Value key) : Object.SlotPayload String Value key :=
  if key == "x" then .computed fun self inherited =>
    (spec.eval self inherited).map (· + 1)
  else spec

/-- Wrapping every direct contribution differs from wrapping the final
result. New layers are not automatically wrapped, and unrelated graph
branches retain their original declarations. -/
private def results : Except String Bool := do
  let original ← source |>.mapError (fun _ => "source")
  let wrapped := original.plan.memoizeCompiled.wrapAncestrySlots addOne
  let indexed := original.plan.memoizeIndexed.wrapAncestrySlots addOne
  let finalOnly ← (original.extendWith "FinalWrapper" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 1)))
    |>.mapError (fun _ => "final wrapper")
  let future ← (wrapped.extendWith "Future" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 3)))
    |>.mapError (fun _ => "future")
  let unused ← Object.compile wrapped.plan.schema "Unused"
    |>.mapError (fun _ => "unused branch")
  let changedDefault := wrapped.transformAncestryDeclarations fun name declaration =>
    if name == "Left" then declaration.withDefault "limit" 9 else declaration
  return original.read "x" == some 12 && wrapped.read "x" == some 16 &&
    indexed.read "x" == some 16 && wrapped.mode == .compiled &&
    indexed.mode == .indexed && wrapped.plan.precedence == original.plan.precedence &&
    wrapped.plan.schema.graph.nodes == original.plan.schema.graph.nodes &&
    wrapped.read "z" == some 5 && wrapped.read "limit" == some 7 &&
    finalOnly.read "x" == some 13 && future.read "x" == some 48 &&
    unused.memoize.read "x" == some 99 && changedDefault.read "limit" == some 9 &&
    changedDefault.read "x" == some 16 && original.read "x" == some 12

#guard match results with
  | .ok true => true
  | _ => false

inductive Key where
  | number | title
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev TypedValue : Key → Type
  | .number => Nat
  | .title => String

private def typedWrapper (_name : String) (key : Key)
    (spec : Object.SlotPayload Key TypedValue key) :
    Object.SlotPayload Key TypedValue key :=
  match key with
  | .number => .computed fun self inherited => (spec.eval self inherited).map (· + 1)
  | .title => .computed fun self inherited => (spec.eval self inherited).map String.toUpper

private def heterogeneous : Except C4.Error Bool := do
  let original ← Object.define (Key := Key) (Value := TypedValue) "Typed" do
    Object.Declaration.Builder.value .number 4
    Object.Declaration.Builder.value .title "widget"
  let wrapped := original.wrapAncestrySlots typedWrapper
  return wrapped.read .number == some 5 && wrapped.read .title == some "WIDGET" &&
    original.read .title == some "widget"

#guard match heterogeneous with
  | .ok true => true
  | _ => false

/-- Absent declarations stay absent even when the generic transformation
would add a method to an existing empty declaration. -/
private def absentDeclaration : Except C4.Error Bool := do
  let schema : Object.Schema String Value :=
    { graph := { nodes := [{ name := "Absent" }] }, declaration := fun _ => none }
  let plan ← Object.compile schema "Absent"
  let revised := plan.transformAncestryDeclarations fun _ declaration =>
    declaration.withValue "x" 100
  return (revised.schema.declaration "Absent").isNone && revised.memoize.read "x" == none

#guard match absentDeclaration with
  | .ok true => true
  | _ => false

/-- Retain last-write-wins for repeated entries before and after wrapping. -/
private def repeatedEntries : Bool :=
  let declaration : Object.Declaration String Value :=
    { slots := [⟨"x", .constant (some 1), fun _ => inferInstance⟩,
        ⟨"x", .constant (some 4), fun _ => inferInstance⟩]
      defaults := [] }
  let mapped := declaration.mapSlots (addOne "Repeat")
  match mapped.slot "x" with
  | some spec => spec.eval (fun _ => none) (fun _ => none) == some 5
  | none => false

#guard repeatedEntries

inductive MethodKey where
  | run | scale
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev MethodValue : MethodKey → Type
  | .run => Nat → Nat
  | .scale => Nat

private def methodWrapper (_name : String) (key : MethodKey)
    (spec : Object.SlotPayload MethodKey MethodValue key) :
    Object.SlotPayload MethodKey MethodValue key :=
  match key with
  | .run => .computed fun self inherited =>
      (spec.eval self inherited).map fun method input => method (input + 3) + 1
  | .scale => spec

/-- Argument/result wrappers still supply the new final self after further
extension; they do not freeze the original method's self-dependent formula. -/
private def methodArguments : Except C4.Error Bool := do
  let original ← Object.define (Key := MethodKey) (Value := MethodValue) "Method" do
    Object.Declaration.Builder.value .scale 5
    Object.Declaration.Builder.slot .run (.self fun self =>
      some fun input => (self .scale).getD 0 * input)
  let wrapped := original.wrapAncestrySlots methodWrapper
  let future ← wrapped.extendWith "NewScale" do
    Object.Declaration.Builder.value .scale 7
  return (original.read .run).map (· 4) == some 20 &&
    (wrapped.read .run).map (· 4) == some 36 &&
    (future.read .run).map (· 4) == some 50

#guard match methodArguments with
  | .ok true => true
  | _ => false

end LeanPoo.Tests.AncestryTransform
