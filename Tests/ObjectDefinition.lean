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
  let sibling ← child.defineWith "Sibling" ["Root"] do
    Object.Declaration.Builder.modifyInherited .derived
      (Option.map (· + 10))
  let diamond ← sibling.defineWith "Diamond"
      ["Child", "Sibling"] do
    pure ()
  let rejectsDuplicate := match root.extendWith "Root" do
      Object.Declaration.Builder.value .source 11 with
    | .error (.duplicateNode "Root") => true
    | _ => false
  let rejectsUnknownParent := match diamond.defineWith "Orphan" ["Missing"] do
      pure () with
    | .error (.unknownNode "Missing") => true
    | _ => false
  return (root.read .derived, child.read .derived,
    diamond.read .derived, diamond.plan.precedence,
    rejectsDuplicate && rejectsUnknownParent)

#guard match scenario with
  | .ok (some 5, some 11, some 21,
      ["Diamond", "Child", "Sibling", "Root"], true) => true
  | _ => false

private def resolutionModeScenario : Except C4.Error Bool := do
  let root ← Object.define (Key := Key) (Value := Value) "Root" do
    Object.Declaration.Builder.value .source 3
  let compiled := root.plan.memoizeCompiled
  let child ← compiled.extendWith "Child" do
    Object.Declaration.Builder.value .source 7
  let sibling ← child.defineWith "Sibling" ["Root"] do
    Object.Declaration.Builder.modifyInherited .source
      (Option.map (· + 1))
  let diamond ← sibling.defineWith "Diamond" ["Child", "Sibling"] do
    pure ()
  return child.mode == .compiled && sibling.mode == .compiled &&
    diamond.mode == .compiled && diamond.read .source == some 7

#guard match resolutionModeScenario with
  | .ok true => true
  | _ => false

private def independentParents : Except Object.CombineError
    (List String × Option Nat × Option Nat × Bool × Bool) := do
  let source ← (Object.define (Key := Key) (Value := Value) "Source" do
    Object.Declaration.Builder.value .source 2).mapError .c4
  let increment ← (Object.define (Key := Key) (Value := Value) "Increment" do
    Object.Declaration.Builder.modifyInherited .derived
      (Option.map (· + 10))).mapError .c4
  let seed ← (Object.define (Key := Key) (Value := Value) "Seed" do
    Object.Declaration.Builder.default .derived 4).mapError .c4
  let indexed := source.plan.memoizeIndexed
  let combined ← indexed.defineFrom "Combined" [increment, seed] do
    pure ()
  let rejectsSharedFamily := match indexed.defineFrom "Repeated" [indexed] do
      pure () with
    | .error (.schema (.duplicateNode "Source")) => true
    | _ => false
  return (combined.plan.precedence, combined.read .source,
    combined.read .derived, combined.mode == .indexed, rejectsSharedFamily)

#guard match independentParents with
  | .ok (["Combined", "Source", "Increment", "Seed"],
      some 2, some 14, true, true) => true
  | _ => false

private def nodeMetadata : Except C4.Error (List String × Option Nat × Bool) := do
  let root ← Object.define (Key := Key) (Value := Value) "Object" do
    Object.Declaration.Builder.default .source 1
  let a ← root.defineWith "A" ["Object"] do
    Object.Declaration.Builder.modifyInherited .source (Option.map (· + 1))
  let b ← a.defineWith "B" ["Object"] do
    Object.Declaration.Builder.modifyInherited .source (Option.map (· + 2))
  let c ← b.defineWith "C" ["Object"] do
    Object.Declaration.Builder.modifyInherited .source (Option.map (· + 3))
  let combined ← c.defineNodeWith
      { name := "Example", parentOrders := [["A", "B"], ["C"]] } do
    pure ()
  let invalid := match c.defineNodeWith
      { name := "Invalid", parentOrders := [["Missing"]] } do pure () with
    | .error (.unknownNode "Missing") => true
    | _ => false
  return (combined.plan.precedence, combined.read .source, invalid)

#guard match nodeMetadata with
  | .ok (["Example", "A", "B", "C", "Object"], some 7, true) => true
  | _ => false

private def suffixMetadata : Except C4.Error (List String × Bool) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let tail ← Object.defineNodeIn empty { name := "Tail", suffix := true } do
    Object.Declaration.Builder.default .source 1
  let other ← tail.defineNodeWith { name := "Other" } do
    Object.Declaration.Builder.value .source 2
  let valid ← other.defineNodeWith
      { name := "Valid", parentOrders := [["Other", "Tail"]] } do
    pure ()
  let rejectsBadOrder := match other.defineNodeWith
      { name := "Bad", parentOrders := [["Tail", "Other"]] } do pure () with
    | .error .suffixOrderViolation => true
    | _ => false
  return (valid.plan.precedence, rejectsBadOrder)

#guard match suffixMetadata with
  | .ok (["Valid", "Other", "Tail"], true) => true
  | _ => false

end LeanPoo.Tests.ObjectDefinition
