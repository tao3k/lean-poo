import LeanPoo.C4.ValidationInvariant

namespace LeanPoo.Tests.ValidationInvariant
open C4 LinearizeState

example {graph : Graph} (unique : (graph.nodes.map Node.name).Nodup)
    (closed : ∀ node ∈ graph.nodes, ∀ parent ∈ node.parentOrders.flatten,
      parent ∈ graph.nodes.map Node.name) : graph.validate = .ok () := Graph.validate_complete unique closed
example (trace : GraphTrace graph root output tail) (unique : ReachableUnique graph root) :
    (Graph.mk (reachableNodes graph root)).validate = .ok () := reachable_validate_complete trace unique
example (trace : GraphTrace graph root output tail) (unique : ReachableUnique graph root) :
    linearize graph root = .ok output ∧ linearizeChecked graph root = .ok output :=
  ⟨linearize_unique_complete trace unique, linearizeChecked_unique_complete trace unique⟩
example (trace : GraphTrace graph root output tail) (unique : (graph.nodes.map Node.name).Nodup) :
    linearize graph root = .ok output := linearize_unique_complete trace (reachableUnique_of_global unique)

private def uniqueNames (nodes : List Node) : Bool :=
  (nodes.map Node.name).all fun name => (nodes.filter (fun node => node.name == name)).length == 1
private def closedNames (nodes : List Node) : Bool :=
  nodes.all fun node => node.parentOrders.flatten.all fun name => (nodes.map Node.name).contains name
private def families : List Graph :=
  [[], ["A"], ["Missing"]].flatMap fun firstParents =>
  [[], ["A"], ["Root"], ["Missing"]].flatMap fun rootParents =>
  [false, true].flatMap fun suffix =>
  [[], [{ name := "Root" }], [{ name := "Broken", parentOrders := [["Missing"]] }],
    [{ name := "Broken" }, { name := "Broken", parentOrders := [["Missing"]] }]].map fun extra =>
  { nodes := [{ name := "A", parentOrders := [[], firstParents, firstParents] },
    { name := "Root", parentOrders := [[], rootParents], suffix := suffix }] ++ extra }

#eval do
  let mut validated := 0
  let mut accepted := 0
  let mut examined := 0
  IO.println s!"VALIDATION-INVARIANT-START graphs={families.length}"
  for graph in families do
    if uniqueNames graph.nodes && closedNames graph.nodes then
      unless graph.validate.toOption.isSome do throw (IO.userError s!"validation mismatch: {repr graph}")
      validated := validated + 1
    if uniqueNames (reachableNodes graph "Root") then
      match reconstruct graph "Root" with
      | .error _ => pure ()
      | .ok result =>
        unless (Graph.mk (reachableNodes graph "Root")).validate.toOption.isSome &&
            (linearize graph "Root").toOption == some result.output &&
            (linearizeChecked graph "Root").toOption == some result.output do
          throw (IO.userError s!"reachable validation or output mismatch: {repr graph}")
        accepted := accepted + 1
    examined := examined + 1
    if examined % 24 == 0 then IO.println s!"VALIDATION-INVARIANT-PROGRESS graphs={examined}"
  IO.println s!"VALIDATION-INVARIANT-OK graphs={examined} validated={validated} accepted={accepted}"

private def disconnected : Graph := { nodes := [{ name := "Root" },
  { name := "Broken" }, { name := "Broken", parentOrders := [["Missing"]] }] }
#guard uniqueNames disconnected.nodes == false
#guard uniqueNames (reachableNodes disconnected "Root") == true
#guard (linearize disconnected "Root").toOption == some ["Root"]
#guard match disconnected.validate with
  | .error (.duplicateNode "Broken") => true
  | _ => false
private def repeated : Graph := { nodes := [{ name := "A" },
  { name := "Root", parentOrders := [[], ["A"], ["A"], []] }] }
#guard repeated.validate.toOption.isSome
#guard (linearize repeated "Root").toOption == some ["Root", "A"]
private def duplicate : Graph := { nodes := [{ name := "Root" }, { name := "Root" }] }
#guard uniqueNames (reachableNodes duplicate "Root") == false
#guard match linearize duplicate "Root" with
  | .error (.duplicateNode "Root") => true
  | _ => false
#guard (reconstruct duplicate "Root").toOption.map (·.output) == some ["Root"]
private def missing : Graph := { nodes := [{ name := "Root", parentOrders := [["Absent"]] }] }
#guard uniqueNames missing.nodes == true
#guard closedNames missing.nodes == false
#guard match missing.validate with
  | .error (.unknownNode "Absent") => true
  | _ => false

#print axioms Graph.validate_complete
#print axioms reachable_declaration_lookup
#print axioms reachable_declarations_closed
#print axioms reachable_validate_complete
#print axioms reachableUnique_of_global
#print axioms linearizeWith_unique_complete
#print axioms linearize_unique_complete
#print axioms linearizeChecked_unique_complete

end LeanPoo.Tests.ValidationInvariant
