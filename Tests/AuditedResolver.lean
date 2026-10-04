import LeanPoo.C4.AuditedResolver

namespace LeanPoo.Tests.AuditedResolver
open C4 LinearizeState

example (success : linearizeAudited graph root = .ok output) :
    ∃ tail, GraphTrace graph root output tail := linearizeAudited_graph_sound success

example (valid : MetadataInvariant graph table)
    (success : resolveAuditedNode (nodeIndex graph) root name table fuel = .ok ready) :
    MetadataInvariant graph ready := (resolveAuditedNode_acceptance valid success).2.2

#eval do
  let mut families := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut cacheCases := 0
  IO.println "AUDITED-RESOLVER-START"
  for p in [[["A"]], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]] do
    for s in [[["A"]], [["B"]], [["A", "B"]], [["B", "A"]]] do
      for flags in List.range 4 do
        for localOrders in [[["P", "S"]], [["S", "P"]], [["P"], ["S"]], [[], ["P", "S"], ["P"], []]] do
          let graph : Graph := { nodes := [
            {name := "A"}, {name := "B"},
            {name := "P", parentOrders := p, suffix := flags % 2 == 1},
            {name := "S", parentOrders := s, suffix := flags / 2 == 1},
            {name := "Root", parentOrders := localOrders}] }
          let index := nodeIndex graph
          let .ok partialCache := resolveNode index "Root" "P" {} true graph.nodes.length
            | throw (IO.userError "canonical partial P cache failed")
          for before in [({} : Table), partialCache] do
            for name in ["P", "Root"] do
              for fuel in List.range (graph.nodes.length + 2) do
                let checkedCache := resolveNode index "Root" name before true fuel
                let auditedCache := resolveAuditedNode index "Root" name before fuel
                match checkedCache, auditedCache with
                | .error _, .error _ => pure ()
                | .ok checkedAfter, .ok auditedAfter =>
                  for declaration in graph.nodes do
                    unless lookup checkedAfter declaration.name == lookup auditedAfter declaration.name do
                      throw (IO.userError "canonical cache entries differ across audited and checked resolution")
                | _, _ => throw (IO.userError "canonical cache success domains differ")
                cacheCases := cacheCases + 1
          let audited := linearizeAudited graph "Root"
          unless audited.toOption == (linearizeChecked graph "Root").toOption do
            throw (IO.userError "audited and checked successful outputs differ")
          match audited with
          | .error _ => rejected := rejected + 1
          | .ok output =>
            unless (linearize graph "Root").toOption == some output do
              throw (IO.userError "audited output differs from ordinary")
            let .ok order := linearizeAuditedVerified graph "Root"
              | throw (IO.userError "verified wrapper rejected an audited success")
            unless order.output == output && order.indexAncestors.isAncestor "A" do
              throw (IO.userError "retained verified order or ancestry query disagrees")
            let index := nodeIndex graph
            let .ok cache := resolveAuditedNode index "Root" "Root" {} graph.nodes.length
              | throw (IO.userError "audited recursion rejected a top-level success")
            unless (lookup cache "Root").map Linearization.precedence == some output do
              throw (IO.userError "audited cache disagrees with top-level result")
            unless (resolveAuditedNode index "Root" "Root" cache 0).toOption.isSome do
              throw (IO.userError "zero-fuel cached result was rejected")
            accepted := accepted + 1
          families := families + 1
          if families % 64 == 0 then IO.println s!"AUDITED-RESOLVER-PROGRESS families={families}"
  IO.println s!"AUDITED-RESOLVER-OK families={families} accepted={accepted} rejected={rejected} cacheCases={cacheCases}"

private def crossing : Graph := { nodes := [
  {name := "A"}, {name := "B"}, {name := "P", parentOrders := [["A", "B"]]},
  {name := "S", parentOrders := [["A"]], suffix := true},
  {name := "Root", parentOrders := [["P", "S"]]}] }
#guard (linearize crossing "Root").toOption == some ["Root", "P", "B", "S", "A"]
#guard (linearizeAudited crossing "Root").toOption.isNone

private def leaf : Graph := {nodes := [{name := "A"}]}
#guard (linearizeAudited leaf "A").toOption == some ["A"]
#guard (resolveAuditedNode (nodeIndex leaf) "A" "A" {} 0).toOption.isNone
#guard (linearizeAudited leaf "Missing").toOption.isNone
#guard (linearizeAudited {nodes := [{name := "A", parentOrders := [["Missing"]]}]} "A").toOption.isNone
#guard (linearizeAudited {nodes := [{name := "A", parentOrders := [["A"]]}]} "A").toOption.isNone
#guard (linearizeAudited {nodes := [{name := "A", parentOrders := [["B"]]},
  {name := "B", parentOrders := [["A"]]}]} "A").toOption.isNone
#guard (linearizeAudited {nodes := [{name := "A"}, {name := "A"}]} "A").toOption.isNone
#guard (linearizeAudited {nodes := [{name := "A"}, {name := "Unused", parentOrders := [["Unknown"]]}]} "A").toOption == some ["A"]

#print axioms computeAuditedNode_checked_complete
#print axioms resolveAuditedNode_checked_complete
#print axioms resolveAuditedNode_success_iff
#print axioms linearizeAudited_checked_complete
#print axioms linearizeAudited_success_iff
#print axioms linearizeAudited_toOption
#print axioms linearizeAuditedVerified_toOption
#print axioms resolveAuditedNode_acceptance
#print axioms resolveAuditedNode_graph_sound
#print axioms linearizeAudited_accepts_mode
#print axioms linearizeAudited_graph_sound
#print axioms linearizeAuditedVerified_projection
#print axioms linearizeAudited_ordinary
end LeanPoo.Tests.AuditedResolver
