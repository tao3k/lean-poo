import LeanPoo.Object.SortedInheritance

/-! Prioritize additive specifications over multiplicative specifications. -/
namespace LeanPoo.Examples.SortedInheritance
open Object SortedInheritance

private def schema : Schema String (fun _ => Nat) :=
  { graph := { nodes := [{ name := "Defaults" },
      { name := "Scale", parentOrders := [["Defaults"]] },
      { name := "Add", parentOrders := [["Defaults"]] },
      { name := "Root", parentOrders := [["Scale"], ["Add"]] }] }
    declaration := fun name =>
      if name == "Defaults" then some (Declaration.empty.withValue "x" 1)
      else if name == "Scale" then some (Declaration.empty.withSlot "x"
        (.computed fun _ next => (next ()).map (· * 2)))
      else if name == "Add" then some (Declaration.empty.withSlot "x"
        (.computed fun _ next => (next ()).map (· + 10)))
      else none }
private def policy : Policy :=
  { sorts := { nodes := [{ name := "Bottom" },
        { name := "High", parentOrders := [["Bottom"]] },
        { name := "Low", parentOrders := [["Bottom"]] },
        { name := "Priority", parentOrders := [["High", "Low"]] }] }
    root := "Priority"
    classification := [("Root", "Priority"), ("Scale", "Low"),
      ("Add", "High"), ("Defaults", "Bottom")] }

private def run : Except String (Nat × Nat × List String × Nat) := do
  let plan ← (Object.compile schema "Root").mapError (fun e => s!"{repr e}")
  let source := plan.memoizeIndexed
  let sorted ← SortedInheritance.apply policy source "Sorted" |>.mapError (fun e => s!"{repr e}")
  let future ← (sorted.object.extend "Future"
    (Declaration.empty.withSlot "x" (.computed fun _ next => (next ()).map (· + 100))))
    |>.mapError (fun e => s!"{repr e}")
  let old ← source.ref "x" |>.mapError (fun _ => "old x")
  let value ← sorted.object.ref "x" |>.mapError (fun _ => "sorted x")
  let later ← future.ref "x" |>.mapError (fun _ => "future x")
  return (old, value, sorted.object.plan.precedence, later)

#guard run.toOption == some (22, 12, ["Sorted", "Root", "Add", "Scale", "Defaults"], 112)
#eval run
end LeanPoo.Examples.SortedInheritance
