import LeanPoo.C4.ReachabilityInvariant

namespace LeanPoo.Tests.ReachabilityInvariant
open C4 LinearizeState

example (graph : Graph) (root name : String) :
    name ∈ reachable graph (nodeIndex graph) root ↔ Ancestor graph name root := reachable_iff graph root name
example (graph : Graph) (root : String) :
    (reachable graph (nodeIndex graph) root).Nodup := reachable_nodup graph root
example (trace : GraphTrace graph root output tail) :
    output.length ≤ (reachableNodes graph root).length := reachableNodes_budget trace
example (trace : GraphTrace graph root output tail)
    (validated : (Graph.mk (reachableNodes graph root)).validate = .ok ()) (checked : Bool) :
    linearizeWith graph root checked = .ok output := linearizeWith_complete trace validated checked
example (trace : GraphTrace graph root output tail)
    (validated : (Graph.mk (reachableNodes graph root)).validate = .ok ()) :
    linearize graph root = .ok output ∧ linearizeChecked graph root = .ok output :=
  ⟨linearize_complete trace validated, linearizeChecked_complete trace validated⟩

/- Independent set saturation uses linear graph lookup and list membership,
not the runtime queue, HashSet, or node index. -/
private def distinct (names : List String) : List String :=
  names.foldl (fun accumulated name => if accumulated.contains name then accumulated else accumulated ++ [name]) []
private def saturate (graph : Graph) : Nat → List String → List String
  | 0, names => names
  | fuel + 1, names =>
    let expanded := names.flatMap fun name =>
      match graph.findNode? name with
      | none => []
      | some node => node.parentOrders.flatten
    saturate graph fuel (distinct (names ++ expanded))
private def families : List Graph :=
  [[], ["B"], ["Missing"]].flatMap fun firstParents =>
  [[], ["A"], ["Root"]].flatMap fun secondParents =>
  [[], ["A"], ["B"], ["A", "B"], ["B", "A"]].flatMap fun rootParents =>
  [false, true].flatMap fun repeats =>
  [[], [{ name := "Root", parentOrders := [["Missing"]] }],
    [{ name := "A", parentOrders := [["Missing"]] }]].flatMap fun duplicates =>
  [false, true].map fun disconnected =>
  let orders := fun names => if repeats then [[], names, names, []] else [names]
  { nodes := [{ name := "A", parentOrders := orders firstParents },
      { name := "B", parentOrders := orders secondParents },
      { name := "Root", parentOrders := orders rootParents }] ++ duplicates ++
      (if disconnected then [{ name := "Broken", parentOrders := [["Nowhere"]] }] else []) }

#eval do
  let mut queries := 0
  let mut accepted := 0
  IO.println s!"REACHABILITY-INVARIANT-START graphs={families.length}"
  for graph in families do
    for root in ["Root", "Absent"] do
      let actual := reachable graph (nodeIndex graph) root
      let expected := saturate graph (graph.nodes.length + 1) [root]
      unless actual.length == expected.length && actual.length == (distinct actual).length &&
          expected.all (fun name => actual.contains name) do
        throw (IO.userError s!"reachability mismatch root={root}: {repr graph}")
      queries := queries + 1
      match reconstruct graph root, (Graph.mk (reachableNodes graph root)).validate with
      | .ok result, .ok () =>
        accepted := accepted + 1
        unless (linearize graph root).toOption == some result.output &&
            (linearizeChecked graph root).toOption == some result.output do
          throw (IO.userError s!"top-level mismatch root={root}: {repr graph}")
      | _, _ => pure ()
      if queries % 180 == 0 then IO.println s!"REACHABILITY-INVARIANT-PROGRESS queries={queries}"
  IO.println s!"REACHABILITY-INVARIANT-OK queries={queries} accepted={accepted}"

private def diamond : Graph := { nodes := [{ name := "A" },
  { name := "B", parentOrders := [["A"]] },
  { name := "Root", parentOrders := [[], ["B", "A"], ["B"], []] },
  { name := "Broken", parentOrders := [["Missing"]] }] }
#guard reachable diamond (nodeIndex diamond) "Root" == ["Root", "B", "A"]
#guard (reachableNodes diamond "Root").length == 3
#guard (linearize diamond "Root").toOption == some ["Root", "B", "A"]
#guard reachable diamond (nodeIndex diamond) "Absent" == ["Absent"]
private def duplicate : Graph := { nodes := diamond.nodes ++ [{ name := "Root" }] }
#guard match linearize duplicate "Root" with
  | .error (.duplicateNode "Root") => true
  | _ => false
#guard (reconstruct duplicate "Root").toOption.map (·.output) == some ["Root", "B", "A"]
private def disconnectedDuplicate : Graph := { nodes := diamond.nodes ++ [{ name := "Broken" }] }
#guard (linearize disconnectedDuplicate "Root").toOption == some ["Root", "B", "A"]
private def missing : Graph := { nodes := [{ name := "Root", parentOrders := [["Missing"]] }] }
#guard reachable missing (nodeIndex missing) "Root" == ["Root", "Missing"]
#guard match linearize missing "Root" with
  | .error (.unknownNode "Missing") => true
  | _ => false
private def cyclic : Graph := { nodes := [{ name := "Root", parentOrders := [["Root"]] }] }
#guard reachable cyclic (nodeIndex cyclic) "Root" == ["Root"]
#guard match linearize cyclic "Root" with
  | .error (.cycle "Root") => true
  | _ => false

#print axioms reachable_walk
#print axioms reachable_queue_drained
#print axioms Ancestor.trans
#print axioms reachable_iff
#print axioms reachableNodes_mem
#print axioms reachableNodes_budget
#print axioms linearizeWith_complete
#print axioms reachable_nodup
#print axioms reachable_trace_names
#print axioms linearize_complete
#print axioms linearizeChecked_complete

end LeanPoo.Tests.ReachabilityInvariant
