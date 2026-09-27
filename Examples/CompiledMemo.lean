import LeanPoo.Object.Memo

open LeanPoo

namespace CompiledMemoExample

private def empty : Object.Schema String (fun _ => Nat) :=
  { graph := { nodes := [] }, declaration := fun _ => none }

private def base : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty
    |>.withDefault "x" 3
    |>.withValue "y" 4

private def parent : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "x"
    (.computed fun _ inherited => (inherited ()).map (· + 2))

/-- The final direct declaration at `x` wins within this node. -/
private def child : Object.Declaration String (fun _ => Nat) :=
  { slots := [
      ⟨"x", .computed (fun _ inherited => (inherited ()).map (· + 100)),
        fun _ => inferInstance⟩,
      ⟨"x", .computed (fun _ inherited => (inherited ()).map (· * 2)),
        fun _ => inferInstance⟩,
      ⟨"z", .self (fun self =>
        some ((self "x").getD 0 + (self "y").getD 0)),
        fun _ => inferInstance⟩ ]
    defaults := (Object.Declaration.empty.withDefault "x" 5).defaults }

private def observed : Option (List (Option Nat) × List (Option Nat)) := do
  let basePlan ← (LeanPoo.mix empty "Base" [] base).toOption
  let parentPlan ← (LeanPoo.extend basePlan.schema "Parent" "Base" parent).toOption
  let plan ← (LeanPoo.extend parentPlan.schema "Child" "Parent" child).toOption
  let sparse := plan.memoize
  let compiled := plan.memoizeCompiled
  let keys := ["x", "y", "z", "missing"]
  return (keys.map sparse.read, keys.map compiled.read)

example : observed = some
    ([some 14, some 4, some 18, none],
     [some 14, some 4, some 18, none]) := by
  native_decide

/-- A chosen method-building strategy persists across derived objects. The
left receiver supplies the strategy when two independent families are mixed. -/
private def evolved : Option Bool := do
  let basePlan ← (LeanPoo.mix empty "Base" [] base).toOption
  let parentPlan ← (LeanPoo.extend basePlan.schema "Parent" "Base" parent).toOption
  let plan ← (LeanPoo.extend parentPlan.schema "Child" "Parent" child).toOption
  let source := plan.memoizeCompiled
  let revised ← (source.reviseDefault "Child" "x" 7).toOption
  let extended ← (revised.extend "Extra"
    (Object.Declaration.empty.withSlot "x"
      (.computed fun _ inherited => (inherited ()).map (· + 1)))).toOption
  let cloned ← (extended.clone "Clone" []).toOption
  let otherPlan ← (LeanPoo.mix empty "Other" []
    (Object.Declaration.empty.withValue "other" 5)).toOption
  let joined ← (cloned.mixWith otherPlan.memoize "Joined"
    Object.Declaration.empty).toOption
  let joinedOpposite ← (otherPlan.memoize.mixWith cloned "JoinedOpposite"
    Object.Declaration.empty).toOption
  return source.mode == .compiled && revised.mode == .compiled &&
    extended.mode == .compiled && cloned.mode == .compiled &&
    joined.mode == .compiled && joinedOpposite.mode == .onDemand &&
    revised.read "x" == some 18 &&
    extended.read "x" == some 19 && cloned.read "x" == some 19 &&
    joined.read "other" == some 5 && joined.read "x" == some 19 &&
    joinedOpposite.read "other" == some 5 &&
    joinedOpposite.read "x" == some 19

example : evolved = some true := by
  native_decide

/-- The one-pass table also follows the validated C4 diamond order. -/
private def diamond : Option (List String × Option Nat × Option Nat) := do
  let root ← (LeanPoo.mix empty "Root" []
    (Object.Declaration.empty.withValue "x" 1)).toOption
  let left ← (LeanPoo.extend root.schema "Left" "Root"
    (Object.Declaration.empty.withSlot "x"
      (.computed fun _ inherited => (inherited ()).map (· + 10)))).toOption
  let right ← (LeanPoo.extend left.schema "Right" "Root"
    (Object.Declaration.empty.withSlot "x"
      (.computed fun _ inherited => (inherited ()).map (· * 2)))).toOption
  let top ← (LeanPoo.mix right.schema "Diamond" ["Left", "Right"]
    (Object.Declaration.empty.withSlot "x"
      (.computed fun _ inherited => (inherited ()).map (· + 3)))).toOption
  return (top.precedence, top.memoize.read "x", top.memoizeCompiled.read "x")

example : diamond = some
    (["Diamond", "Left", "Right", "Root"], some 15, some 15) := by
  native_decide

end CompiledMemoExample
