import LeanPoo.C4.Diagnostics

namespace LeanPoo.Tests.Diagnostics
open C4 LinearizeState

example (receipt : RejectedOrder graph root) : ¬ Nonempty (VerifiedOrder graph root) :=
  receipt.noVerified

example (receipt : RejectedOrder graph root) (unique : ReachableUnique graph root) :
    ¬ ∃ output tail, GraphTrace graph root output tail := receipt.noGraphTrace unique

/-- Prefix inconsistency and a parent suffix crossing occur together, so the
ordinary-first audit and full-parent checked compiler report different errors. -/
private def priorityGraph : Graph := { nodes := [
 {name := "A"}, {name := "B"}, {name := "C"},
 {name := "P", parentOrders := [["A", "B", "C"]]},
 {name := "Q", parentOrders := [["C", "B"]]},
 {name := "S", parentOrders := [["A"]], suffix := true},
 {name := "Root", parentOrders := [["P", "Q", "S"]]}] }
#guard (linearizeAudited priorityGraph "Root").toOption.isNone

private def errorOf (result : Except Error α) : Option Error :=
  match result with | .error error => some error | .ok _ => none
#guard errorOf (linearize priorityGraph "Root") == some .inconsistentOrder
#guard errorOf (linearizeAudited priorityGraph "Root") == some .inconsistentOrder
#guard errorOf (linearizeChecked priorityGraph "Root") == some .suffixOrderViolation

private def rootNode : Node := {name := "Root"}
private def duplicateGraph : Graph := {nodes := [rootNode, rootNode]}
private def leafCertificate : NodeCertified "Root" [] [] where
  selection := ⟨[], .inl ⟨rfl, rfl⟩, by simp⟩
  ancestry := ⟨[], .done rfl, by simp⟩
  tailUnique := by simp
  fresh := by simp [SuffixCertified.output]

/-- Graph lookup takes the first declaration, while validation rejects the
second. Original finite graph evidence alone does not certify validation. -/
theorem duplicateGraph_trace : GraphTrace duplicateGraph "Root" ["Root"] [] :=
  .node (show duplicateGraph.findNode? "Root" = some rootNode by rfl) [] rfl (by simp) leafCertificate
#guard errorOf (linearizeAudited duplicateGraph "Root") == some (.duplicateNode "Root")
#guard errorOf (linearizeChecked duplicateGraph "Root") == some (.duplicateNode "Root")

#eval do
  IO.println "DIAGNOSTICS-START"
  let fixtures : List (Graph × String) := [
    (priorityGraph, "Root"), (duplicateGraph, "Root"),
    ({nodes := [rootNode]}, "Root"), ({nodes := [rootNode]}, "Missing"),
    ({nodes := [{name := "Root", parentOrders := [["Missing"]]}]}, "Root"),
    ({nodes := [{name := "Root", parentOrders := [["Root"]]}]}, "Root"),
    ({nodes := [{name := "A", suffix := true}, {name := "B", suffix := true},
      {name := "Root", parentOrders := [["A", "B"]]}]}, "Root"),
    ({nodes := [{name := "A"}, {name := "B"},
      {name := "P", parentOrders := [["A", "B"]]},
      {name := "S", parentOrders := [["A"]], suffix := true},
      {name := "Root", parentOrders := [["P", "S"]]}]}, "Root")]
  let mut accepted := 0
  let mut rejected := 0
  for (graph, root) in fixtures do
    match diagnoseAudited graph root, linearizeAudited graph root with
    | .ok order, .ok output =>
      unless order.output == output do throw (IO.userError "accepted diagnostic projection changed")
      accepted := accepted + 1
    | .error receipt, .error error =>
      unless receipt.error == error do throw (IO.userError "rejected diagnostic projection changed")
      rejected := rejected + 1
    | _, _ => throw (IO.userError "diagnostic outcome changed")
  IO.println s!"DIAGNOSTICS-OK fixtures={fixtures.length} accepted={accepted} rejected={rejected} priority=distinct duplicate=trace-and-rejection"

#print axioms diagnoseAudited_projection
#print axioms RejectedOrder.noVerified
#print axioms RejectedOrder.checkedRejected
#print axioms linearizeAudited_graph_iff
#print axioms RejectedOrder.noGraphTrace
#print axioms linearizeAudited_rejection_iff
#print axioms duplicateGraph_trace
end LeanPoo.Tests.Diagnostics
