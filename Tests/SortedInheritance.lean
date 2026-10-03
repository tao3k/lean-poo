import LeanPoo.Object.SortedInheritance

namespace LeanPoo.Tests.SortedInheritance
open Object SortedInheritance

private def sorts : C4.Graph :=
  { nodes := [{ name := "Bottom" },
      { name := "High", parentOrders := [["Bottom"]] },
      { name := "Low", parentOrders := [["Bottom"]] },
      { name := "Priority", parentOrders := [["High", "Low"]] }] }
private def policy : Policy :=
  { sorts, root := "Priority", classification :=
      [("Root", "Priority"), ("Scale", "Low"), ("Add", "High"), ("Defaults", "Bottom")] }

private def initial (constrained : Bool := false) (suffix : Bool := false) :
    Except C4.Error (Memoized String (fun _ => Nat)) := do
  let empty : Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let defaults := (Declaration.empty : Declaration String (fun _ => Nat))
    |>.withValue "x" 1
    |>.withSlot "self" (.self fun self => (self "x").map (· + 3))
    |>.withDefault "z" 7
  let base ← LeanPoo.mix empty "Defaults" [] defaults
  let scale ← LeanPoo.mixC4 base.schema
    { name := "Scale", parentOrders := [["Defaults"]], suffix }
    (Declaration.empty.withSlot "x" (.computed fun _ next => (next ()).map (· * 2)))
  let add ← LeanPoo.extend scale.schema "Add" "Defaults"
    (Declaration.empty.withSlot "x" (.computed fun _ next => (next ()).map (· + 10)))
  let root ← LeanPoo.mixC4 add.schema
    { name := "Root", parentOrders := if constrained then [["Scale", "Add"]] else [["Scale"], ["Add"]] }
    (Declaration.empty.withSlot "root" (.self fun self => (self "x").map (· * 3)))
  return root.memoize

private def behavior (mode : ResolutionMode) : Except String Bool := do
  let source ← initial |>.mapError (fun _ => "initial")
  let source := source.plan.memoizeUsing mode
  let sorted ← SortedInheritance.apply policy source "Sorted" |>.mapError (fun e => s!"{repr e}")
  let sameSort := { policy with classification :=
    [("Root", "Priority"), ("Scale", "High"), ("Add", "High"), ("Defaults", "Bottom")] }
  let tied ← SortedInheritance.apply sameSort source "Tied" |>.mapError (fun _ => "same sort")
  let future ← sorted.object.extend "Future"
    (Declaration.empty.withSlot "x" (.computed fun _ next => (next ()).map (· + 100)))
    |>.mapError (fun _ => "future")
  let futurePolicy := { policy with classification := policy.classification ++
    [("Sorted", "Priority"), ("Future", "Priority")] }
  let rechecked ← SortedInheritance.apply futurePolicy future "Rechecked" |>.mapError (fun _ => "recheck")
  return sorted.priority == ["Priority", "High", "Low", "Bottom"] &&
    source.plan.precedence == ["Root", "Scale", "Add", "Defaults"] &&
    sorted.object.plan.precedence == ["Sorted", "Root", "Add", "Scale", "Defaults"] &&
    source.read "x" == some 22 && source.read "self" == some 25 &&
    sorted.object.read "x" == some 12 && sorted.object.read "self" == some 15 &&
    sorted.object.read "root" == some 36 && sorted.object.read "z" == some 7 &&
    sorted.object.mode == mode &&
    tied.object.plan.precedence == ["Tied", "Root", "Scale", "Add", "Defaults"] &&
    tied.object.read "x" == some 22 &&
    future.read "x" == some 112 && rechecked.object.read "self" == some 115 &&
    rechecked.object.mode == mode &&
    source.plan.schema.graph.nodes.length == 4 && sorted.object.plan.schema.graph.nodes.length == 5

#guard (behavior .onDemand).toOption == some true
#guard (behavior .compiled).toOption == some true
#guard (behavior .indexed).toOption == some true

private def errors : Except C4.Error Bool := do
  let source ← initial
  let fixed ← initial true
  let duplicate := { policy with classification := policy.classification ++ [("Root", "Priority")] }
  let absent := { policy with classification := policy.classification.filter (·.1 != "Scale") }
  let foreign := { policy with classification := policy.classification ++ [("Ghost", "High")] }
  let unknownSort := { policy with classification := [("Root", "Absent")] }
  let badSorts := { policy with sorts := { nodes := [{ name := "Priority", parentOrders := [["Missing"]] }] } }
  let cycle := { policy with sorts := { nodes :=
    [{ name := "Priority", parentOrders := [["High"]] }, { name := "High", parentOrders := [["Priority"]] }] } }
  let rootLow := { policy with classification :=
    [("Root", "Low"), ("Scale", "Low"), ("Add", "High"), ("Defaults", "Bottom")] }
  return (
    (match SortedInheritance.apply duplicate source "Duplicate" with
      | .error (.repeatedClassification "Root") => true | _ => false) &&
    (match SortedInheritance.apply absent source "Absent" with
      | .error (.unclassified "Scale") => true | _ => false) &&
    (match SortedInheritance.apply foreign source "Foreign" with
      | .error (.unknownSpecification "Ghost") => true | _ => false) &&
    (match SortedInheritance.apply unknownSort source "UnknownSort" with
      | .error (.unavailableSort "Root" "Absent") => true | _ => false) &&
    (match SortedInheritance.apply badSorts source "BadSorts" with
      | .error (.sorts (.unknownNode "Missing")) => true | _ => false) &&
    (match SortedInheritance.apply cycle source "Cycle" with
      | .error (.sorts (.cycle _)) => true | _ => false) &&
    (match SortedInheritance.apply policy fixed "Fixed" with
      | .error (.inheritance .inconsistentOrder pairs) => pairs.contains ("Add", "Scale") | _ => false) &&
    (match SortedInheritance.apply rootLow source "RootLow" with
      | .error (.inheritance .inconsistentOrder pairs) => pairs.contains ("Add", "Root") | _ => false) &&
    (match SortedInheritance.apply policy source "Root" with
      | .error (.inheritance (.duplicateNode "Root") _) => true | _ => false))

#guard errors.toOption == some true

private def suffixConflict : Except C4.Error Bool := do
  let source ← initial false true
  let reversed := { policy with classification :=
    [("Root", "Priority"), ("Scale", "High"), ("Add", "Low"), ("Defaults", "Bottom")] }
  return match SortedInheritance.apply reversed source "SuffixConflict" with
    | .error (.inheritance .suffixOrderViolation pairs) => pairs.contains ("Scale", "Add")
    | .error (.inheritance .inconsistentOrder pairs) => pairs.contains ("Scale", "Add")
    | _ => false

#guard suffixConflict.toOption == some true

inductive Key where
  | amount | render | call
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Value : Key → Type
  | .amount => Nat
  | .render => String
  | .call => Nat → Nat

private def heterogeneous : Except String Bool := do
  let defaults : Declaration Key Value := Declaration.empty
    |>.withValue .amount 1
    |>.withSlot .render (.self fun self => (self .amount).map toString)
    |>.withSlot .call (.self fun self => (self .amount).map fun amount => (· + amount))
  let scale : Declaration Key Value := Declaration.empty
    |>.withSlot .amount (.computed fun _ next => (next ()).map (· * 2))
  let add : Declaration Key Value := Declaration.empty
    |>.withSlot .amount (.computed fun _ next => (next ()).map (· + 10))
  let schema : Schema Key Value :=
    { graph := { nodes := [{ name := "Defaults" },
        { name := "Scale", parentOrders := [["Defaults"]] },
        { name := "Add", parentOrders := [["Defaults"]] },
        { name := "Root", parentOrders := [["Scale"], ["Add"]] }] }
      declaration := fun name => if name == "Defaults" then some defaults
        else if name == "Scale" then some scale else if name == "Add" then some add else none }
  let plan ← (Object.compile schema "Root").mapError (fun _ => "heterogeneous plan")
  let sorted ← SortedInheritance.apply policy plan.memoizeIndexed "TypedSorted"
    |>.mapError (fun _ => "heterogeneous sorting")
  let future ← (sorted.object.extend "TypedFuture" (Declaration.empty.withValue .amount 20))
    |>.mapError (fun _ => "heterogeneous future")
  return sorted.object.read .amount == some 12 && sorted.object.read .render == some "12" &&
    (sorted.object.read .call).map (· 5) == some 17 &&
    future.read .render == some "20" && (future.read .call).map (· 5) == some 25

#guard heterogeneous.toOption == some true

#print axioms requirements_complete
#print axioms Certified.higher_precedes
end LeanPoo.Tests.SortedInheritance
