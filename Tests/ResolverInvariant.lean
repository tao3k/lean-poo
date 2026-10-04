import LeanPoo.C4.ResolverInvariant

namespace LeanPoo.Tests.ResolverInvariant
open C4 LinearizeState

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (budget : output.length ≤ fuel) :
    ∃ ready, resolveNode (nodeIndex graph) root name table checked fuel = .ok ready ∧
      MetadataInvariant graph ready ∧ CacheGrowth table ready (fun item => item ∈ output) ∧
      ∃ result, lookup ready name = some result ∧ result.precedence = output :=
  resolveNode_complete valid trace budget

example (trace : GraphTrace graph root output tail) (checked : Bool) :
    ∃ table, resolveNode (nodeIndex graph) root root {} checked graph.nodes.length = .ok table ∧
      MetadataInvariant graph table ∧ ∃ entry, lookup table root = some entry ∧ entry.precedence = output :=
  resolveNode_graph_complete trace checked

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (budget : output.length ≤ fuel) :
    ((resolveNode (nodeIndex graph) root name table checked fuel).toOption.bind
      (fun ready => lookup ready name)).map (·.precedence) = some output :=
  resolveNode_output valid trace budget

example (growth : CacheGrowth before after (fun item => item ∈ output.tail))
    (trace : GraphTrace graph name output tail) (absent : lookup before name = none) :
    lookup after name = none := growth.fresh absent trace.root_not_tail

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (budget : output.length ≤ fuel)
    (cached : lookup table oldName = some oldEntry) :
    ∃ ready, resolveNode (nodeIndex graph) root name table checked fuel = .ok ready ∧
      lookup ready oldName = some oldEntry := by
  obtain ⟨ready, computed, _, growth, _⟩ :=
    resolveNode_complete (root := root) (checked := checked) valid trace budget
  exact ⟨ready, computed, growth.retains oldName oldEntry cached⟩

private def orders (repeated : Bool) (order : List String) : List (List String) :=
  if repeated then [[], order, order, []] else [order]
private def families : List Graph :=
  [false, true].flatMap fun firstFlag =>
  [false, true].flatMap fun secondFlag =>
  [false, true].flatMap fun rootFlag =>
  [[], ["A"]].flatMap fun secondParents =>
  [[], ["A"], ["B"], ["A", "B"], ["B", "A"]].flatMap fun rootParents =>
  [false, true].flatMap fun secondRepeat =>
  [false, true].map fun rootRepeat =>
  { nodes := [
    { name := "A", suffix := firstFlag },
    { name := "B", parentOrders := orders secondRepeat secondParents, suffix := secondFlag },
    { name := "Root", parentOrders := orders rootRepeat rootParents, suffix := rootFlag }] }
private def resolvedOutput (graph : Graph) (checked : Bool) (fuel : Nat) : Option (List String) :=
  ((resolveNode (nodeIndex graph) "Root" "Root" {} checked fuel).toOption.bind
    (fun ready => lookup ready "Root")).map (·.precedence)

/- Independent successful graph reconstruction is the finite oracle. Error
payload equivalence and whole linearizeWith validation are separate claims. -/
#eval do
  let mut accepted := 0
  let mut checkedGraphs := 0
  IO.println s!"RESOLVER-INVARIANT-START families={families.length}"
  for graph in families do
    match reconstruct graph "Root" with
    | .error _ => pure ()
    | .ok result =>
      accepted := accepted + 1
      for checked in [false, true] do
        unless resolvedOutput graph checked graph.nodes.length == some result.output do
          throw (IO.userError s!"resolver mismatch checked={checked}: {repr graph}")
    checkedGraphs := checkedGraphs + 1
    if checkedGraphs % 80 == 0 then IO.println s!"RESOLVER-INVARIANT-PROGRESS families={checkedGraphs}"
  IO.println s!"RESOLVER-INVARIANT-OK families={checkedGraphs} accepted={accepted}"

private def chain : Graph := { nodes := [
  { name := "A", suffix := true },
  { name := "B", parentOrders := [["A"]], suffix := true },
  { name := "Root", parentOrders := [[], ["B"], ["B"], []] }] }
#guard resolvedOutput chain false 3 == some ["Root", "B", "A"]
#guard resolvedOutput chain true 3 == some ["Root", "B", "A"]
#guard match resolveNode (nodeIndex chain) "Root" "Root" {} false 2 with
  | .error (.cycle "Root") => true
  | _ => false
private def warm : Table := ({} : Table).insert "Root" ⟨["Root", "B", "A"], some "B", some "B"⟩
#guard ((resolveNode ({} : Std.HashMap String Node) "Other" "Root" warm true 0).toOption.bind
  (fun table => lookup table "Root")) == lookup warm "Root"
#guard match resolveNode (nodeIndex chain) "Root" "Missing" {} false 1 with
  | .error (.unknownNode "Missing") => true
  | _ => false
private def cyclic : Graph := { nodes := [{ name := "Root", parentOrders := [["Root"]] }] }
#guard match resolveNode (nodeIndex cyclic) "Root" "Root" {} true 1 with
  | .error (.cycle "Root") => true
  | _ => false

#print axioms CacheGrowth.trans
#print axioms CacheGrowth.fresh
#print axioms CacheGrowth.insert
#print axioms resolveParents_complete
#print axioms GraphTrace.parent_ancestry
#print axioms GraphTrace.root_not_tail
#print axioms resolveNode_cached
#print axioms resolveNode_complete
#print axioms resolveNode_graph_complete
#print axioms resolveNode_output

end LeanPoo.Tests.ResolverInvariant
