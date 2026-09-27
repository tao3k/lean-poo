import LeanPoo.Prototype.Mutable

open LeanPoo

namespace MutablePrototypeExample

private def empty : Object.Schema String (fun _ => Nat) :=
  { graph := { nodes := [] }, declaration := fun _ => none }

private def base : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withValue "count" 2

private def parent : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "count"
    (.computed fun _ inherited => (inherited ()).map (· + 1))

private def child : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty
    |>.withSlot "count" (.computed fun _ inherited =>
      (inherited ()).map (· * 2))
    |>.withSlot "derived" (.self fun self =>
      (self "count").map (· + 10))

private def purePlan : Except C4.Error (Object.Plan String (fun _ => Nat)) := do
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let parentPlan ← LeanPoo.extend basePlan.schema "Parent" "Base" parent
  LeanPoo.extend parentPlan.schema "Child" "Parent" child

private def layers : Prototype.MutableProto String (fun _ => Nat) :=
  Prototype.MutableProto.composeAll [
    .extend "Child" child,
    .extend "Parent" parent ]

/-- Effectful parent-then-child composition uses the same C4 result as pure
extension. A later base edit rebinds the final self; a failed construction
does not expose its partially built private identity. -/
private def run : IO Bool := do
  let some basePlan := (LeanPoo.mix empty "Base" [] base).toOption
    | return false
  let some expected := purePlan.toOption | return false
  let some expectedRevised :=
      (expected.reviseDeclaration "Base"
        (fun declaration => declaration.withValue "count" 4)).toOption
    | return false
  let some object := (← layers.instantiate basePlan.memoize).toOption
    | return false
  let first ← object.snapshot
  let firstCount ← object.read "count"
  let firstDerived ← object.read "derived"
  let sequential ← Object.Mutable.new basePlan.memoize
  let sequentialResult ← layers.apply sequential
  let sequentialSucceeded := match sequentialResult with
    | .ok () => true
    | .error _ => false
  let sequentialCount ← sequential.read "count"
  let sequentialDerived ← sequential.read "derived"
  let some compiledObject :=
      (← layers.instantiateCompiled basePlan.memoize).toOption
    | return false
  let compiledCount ← compiledObject.read "count"
  let compiledDerived ← compiledObject.read "derived"
  let update := Prototype.MutableProto.compose
    (.revise "Base" fun declaration => declaration.withValue "count" 4)
    layers
  let some revised := (← update.instantiate basePlan.memoize).toOption
    | return false
  let second ← revised.snapshot
  let secondCount ← revised.read "count"
  let secondDerived ← revised.read "derived"
  let scale : Prototype.MutableProto String (fun _ => Nat) :=
    .slot "Scale" "count"
      (.computed fun _ inherited => (inherited ()).map (· * 3))
  let some scaled :=
      (← (Prototype.MutableProto.compose scale layers).instantiate
        basePlan.memoize).toOption
    | return false
  let some expectedScaled :=
      (LeanPoo.extend expected.schema "Scale" "Child"
        (Object.Declaration.empty.withSlot "count"
          (.computed fun _ inherited =>
            (inherited ()).map (· * 3)))).toOption
    | return false
  let scaledCount ← scaled.read "count"
  let scaledDerived ← scaled.read "derived"
  let bad := Prototype.MutableProto.compose
    (.extend "Parent" parent) (.extend "Parent" parent)
  let rejected ← bad.instantiate basePlan.memoize
  let shared ← Object.Mutable.new basePlan.memoize
  let sharedResult ← bad.apply shared
  let sharedCount ← shared.read "count"
  let duplicateRejected := match rejected with
    | .error (.duplicateNode "Parent") => true
    | _ => false
  let sharedPartial := match sharedResult with
    | .error (.duplicateNode "Parent") => sharedCount == some 3
    | _ => false
  let custom : Prototype.MutableProto String (fun _ => Nat) :=
    { apply := fun target => target.extend "Custom" child }
  let some fallback :=
      (← (Prototype.MutableProto.compose custom
        (.extend "Parent" parent)).instantiate basePlan.memoize).toOption
    | return false
  let fallbackCount ← fallback.read "count"
  return first.plan.precedence == ["Child", "Parent", "Base"] &&
    first.plan.precedence == expected.precedence &&
    firstCount == expected.memoize.read "count" &&
    firstDerived == expected.memoize.read "derived" &&
    compiledCount == firstCount && compiledDerived == firstDerived &&
    firstCount == some 6 && firstDerived == some 16 &&
    sequentialSucceeded &&
    sequentialCount == firstCount && sequentialDerived == firstDerived &&
    second.plan.precedence == first.plan.precedence &&
    secondCount == some 10 && secondDerived == some 20 &&
    secondCount == expectedRevised.memoize.read "count" &&
    secondDerived == expectedRevised.memoize.read "derived" &&
    scaledCount == some 18 && scaledDerived == some 28 &&
    scaledCount == expectedScaled.memoize.read "count" &&
    scaledDerived == expectedScaled.memoize.read "derived" &&
    basePlan.memoize.read "count" == some 2 &&
    (first.read "count", first.read "derived") == (some 6, some 16) &&
    duplicateRejected && sharedPartial && fallbackCount == some 6

#eval (do
  unless ← run do
    throw (IO.userError "mutable prototype composition failed") : IO Unit)

end MutablePrototypeExample
