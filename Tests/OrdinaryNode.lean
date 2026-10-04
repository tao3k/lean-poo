import LeanPoo.C4.OrdinaryNode

namespace LeanPoo.Tests.OrdinaryNode
open C4 LinearizeState

example (valid : MetadataInvariant graph table)
    (compatible : ParentCompatible table node) (unique : result.precedence.Nodup)
    (ordinary : computeNode table node false = .ok result) :
    computeNode table node true = .ok result := computeNode_ordinary_checked valid compatible unique ordinary

example (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (ordinary : computeNode table node false = .ok result)
    (audited : auditNode table node result = .ok ()) :
    GraphTrace graph node.name result.precedence
      (if node.suffix then result.precedence else selectedTail table result.inheritedSuffix) :=
  computeNode_audited_graph_sound valid found ordinary audited

example (valid : MetadataInvariant graph table)
    (ordinary : computeNode table node false = .ok result) :
    auditNode table node result = .ok () ↔ computeNode table node true = .ok result :=
  auditNode_acceptance_iff valid ordinary

example (receipt : AuditedNode table node) (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node) (fresh : lookup table node.name = none) :
    MetadataInvariant graph (table.insert node.name receipt.result) := receipt.insertSound valid found fresh

#eval do
  let mut families := 0
  let mut ordinaryAccepted := 0
  let mut promoted := 0
  let mut rejected := 0
  IO.println "ORDINARY-NODE-START"
  for p in [[["A"]], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]] do
    for s in [[["A"]], [["B"]], [["A", "B"]], [["B", "A"]]] do
      for flags in List.range 4 do
        for localOrders in [[["P", "S"]], [["S", "P"]], [["P"], ["S"]], [[], ["P", "S"], ["P"], []]] do
          let node : Node := {name := "Root", parentOrders := localOrders}
          let graph : Graph := { nodes := [
            {name := "A"}, {name := "B"},
            {name := "P", parentOrders := p, suffix := flags % 2 == 1},
            {name := "S", parentOrders := s, suffix := flags / 2 == 1}, node] }
          let index := nodeIndex graph
          let .ok first := resolveNode index "Root" "P" {} true graph.nodes.length
            | throw (IO.userError "canonical P resolution failed")
          let .ok table := resolveNode index "Root" "S" first true graph.nodes.length
            | throw (IO.userError "canonical S resolution failed")
          match computeNode table node false with
          | .error _ => pure ()
          | .ok result =>
            ordinaryAccepted := ordinaryAccepted + 1
            match auditNode table node result with
            | .ok () =>
              unless (computeNode table node true).toOption == some result do
                throw (IO.userError "audited result changed in checked execution")
              let .ok receipt := computeAuditedNode table node
                | throw (IO.userError "retained audit wrapper rejected a promoted result")
              unless receipt.result == result do throw (IO.userError "retained result changed")
              promoted := promoted + 1
            | .error _ =>
              unless (computeNode table node true).toOption.isNone do
                throw (IO.userError "audit rejected a checked success")
              unless (computeAuditedNode table node).toOption.isNone do
                throw (IO.userError "retained wrapper accepted a rejected result")
              rejected := rejected + 1
          families := families + 1
          if families % 64 == 0 then IO.println s!"ORDINARY-NODE-PROGRESS families={families}"
  IO.println s!"ORDINARY-NODE-OK families={families} ordinary={ordinaryAccepted} promoted={promoted} rejected={rejected}"

/- Audit success alone does not certify an invented output. The promotion
API also requires the receipt of the exact ordinary execution. -/
private def emptyRoot : Node := {name := "Root"}
private def invented : Linearization := ⟨["Invented"], none, none⟩
#guard (auditNode {} emptyRoot invented).toOption.isSome
#guard (computeNode {} emptyRoot false).toOption != some invented
example : ¬ ∃ tail, GraphTrace ({nodes := [emptyRoot]} : Graph) "Root" invented.precedence tail := by
  rintro ⟨_, trace⟩
  have member := trace.root_mem
  simp [invented] at member

private def repeated : Linearization := ⟨["Root", "Root"], none, none⟩
#guard match auditNode {} emptyRoot repeated with
  | .error .inconsistentOrder => true
  | _ => false

#print axioms AuditedNode.checked
#print axioms AuditedNode.graphSound
#print axioms AuditedNode.insertSound
#print axioms computeNode_ordinary_evidence
#print axioms computeNode_ordinary_checked
#print axioms computeNode_checked_iff
#print axioms computeNode_ordinary_graph_sound
#print axioms auditNode_sound
#print axioms auditNode_complete
#print axioms auditNode_acceptance_iff
#print axioms computeNode_audited_graph_sound
end LeanPoo.Tests.OrdinaryNode
