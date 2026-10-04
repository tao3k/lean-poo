import LeanPoo.C4.NodeSoundness

namespace LeanPoo.Tests.NodeSoundness
open C4 LinearizeState

example (certificate : TailCertified (tails.filter (fun tail => !tail.isEmpty))) :
    ∃ original : TailCertified tails, original.output = certificate.output := certificate.restore_empty
example (certificate : NodeCertified name orders (tails.filter (fun tail => !tail.isEmpty))) :
    ∃ original : NodeCertified name orders tails,
      original.output = certificate.output ∧ original.selection.output = certificate.selection.output :=
  certificate.restore_empty
example (certificate : NodeCertified name
    ((unique names).map order ++ MergeState.pending locals) ((unique names).map parentTail)) :
    ∃ original : NodeCertified name (names.map order ++ locals) (names.map parentTail),
      original.output = certificate.output ∧ original.selection.output = certificate.selection.output :=
  nodeCertificate_expand certificate
example (valid : MetadataInvariant graph table) (found : graph.findNode? node.name = some node)
    (success : computeNode table node true = .ok result) :
    GraphTrace graph node.name result.precedence
      (if node.suffix then result.precedence else selectedTail table result.inheritedSuffix) :=
  computeNode_checked_graph_sound valid found success
example (valid : MetadataInvariant graph table) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none) (success : computeNode table node true = .ok result) :
    MetadataInvariant graph (table.insert node.name result) :=
  computeNode_checked_insert_sound valid found fresh success

private def words : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => ["A", "B"].map (· :: rest)
private def order (name : String) : List String := [name]
private def tail (marked : Bool) (name : String) : List String := if marked then [name] else []
#eval do
  let mut families := 0
  let mut accepted := 0
  IO.println "NODE-SOUNDNESS-START"
  for names in (List.range 5).flatMap words do
    for locals in [[], [[]], [["A", "B"]], [[], ["B", "A"], []]] do
      for marked in [false, true] do
        let normalizedOrders := (unique names).map order ++ MergeState.pending locals
        let normalizedTails := (unique names).map (tail marked)
        for claimed in [[], ["A"], ["B"]] do
          match certifyNode "Root" normalizedOrders
              (normalizedTails.filter (fun tail => !tail.isEmpty)) claimed with
          | .error _ => pure ()
          | .ok certificate =>
            match certifyNode "Root" (names.map order ++ locals) (names.map (tail marked)) claimed with
            | .error error => throw (IO.userError s!"expansion rejected: {repr error}")
            | .ok original =>
              unless original.output == certificate.output && original.selection.output == certificate.selection.output do
                throw (IO.userError "expansion output mismatch")
            accepted := accepted + 1
          families := families + 1
          if families % 186 == 0 then IO.println s!"NODE-SOUNDNESS-PROGRESS families={families}"
  IO.println s!"NODE-SOUNDNESS-OK families={families} accepted={accepted}"

/- Empty-tail restoration includes nonempty all-empty input, and a different
claimed tail cannot be invented by restoring empties. -/
#guard (certifyNode "Root" [] [[], [], []] []).toOption.map (·.output) == some ["Root"]
#guard (certifyNode "Root" [] [[], [], []] ["Invented"]).toOption.isSome == false
private def repeatedGraph : Graph := { nodes := [{ name := "A" }, { name := "B" },
  { name := "Root", parentOrders := [[], ["A", "B"], ["A"], []] }] }
#guard (reconstruct repeatedGraph "Root").toOption.map (·.output) ==
  (linearizeChecked repeatedGraph "Root").toOption

#print axioms TailCertified.restore_empty
#print axioms NodeCertified.restore_empty
#print axioms nodeCertificate_expand
#print axioms checked_certificate_graph
#print axioms computeNode_checked_graph_sound
#print axioms computeNode_checked_insert_sound

end LeanPoo.Tests.NodeSoundness
