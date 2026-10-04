import LeanPoo.C4.CertificateExpansion

namespace LeanPoo.C4.LinearizeState

private theorem cast_node_outputs (ordersSame : orders = otherOrders) (tailsSame : tails = otherTails)
    (certificate : NodeCertified name orders tails) :
    (tailsSame ▸ ordersSame ▸ certificate : NodeCertified name otherOrders otherTails).output = certificate.output ∧
      (tailsSame ▸ ordersSame ▸ certificate : NodeCertified name otherOrders otherTails).selection.output =
        certificate.selection.output := by
  cases ordersSame; cases tailsSame; exact ⟨rfl, rfl⟩

/-- Lift the actual normalized certificate to all original declared graph rows,
using canonical parent metadata. Root graph evidence is not a premise. -/
theorem checked_certificate_graph (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries)
    (certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix)))) :
    GraphTrace graph node.name certificate.output
      (if node.suffix then certificate.output else certificate.selection.output) := by
  have available := collected_suffix_available valid collected
  have tailsSame := suffixTails_drop_empty valid.suffixes available
  let filtered : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      ((entries.map (·.mostSpecificSuffix)).map (selectedTail table) |>.filter (fun tail => !tail.isEmpty)) :=
    tailsSame ▸ certificate
  have filteredOutputs := cast_node_outputs rfl tailsSame certificate
  obtain ⟨restored, restoredOutput, restoredTail⟩ := filtered.restore_empty
  have ordersSame : entries.map (·.precedence) ++ MergeState.pending node.parentOrders =
      (unique node.parentOrders.flatten).map (cachedOrder table) ++ MergeState.pending node.parentOrders :=
    congrArg (· ++ MergeState.pending node.parentOrders) (collected_precedence_map collected)
  have parentTails : (entries.map (·.mostSpecificSuffix)).map (selectedTail table) =
      (unique node.parentOrders.flatten).map (cachedParentTail table) := by
    simpa only [parents, List.map_map, Function.comp_def] using collected_parent_tail_map collected
  let normalized : NodeCertified node.name
      ((unique node.parentOrders.flatten).map (cachedOrder table) ++ MergeState.pending node.parentOrders)
      ((unique node.parentOrders.flatten).map (cachedParentTail table)) := parentTails ▸ ordersSame ▸ restored
  have normalizedOutputs := cast_node_outputs ordersSame parentTails restored
  obtain ⟨original, originalOutput, originalTail⟩ := nodeCertificate_expand normalized
  let rows := node.parentOrders.flatten.map fun name => (name, (cachedOrder table name, cachedParentTail table name))
  have rowOrders : rows.map (fun row => row.2.1) = node.parentOrders.flatten.map (cachedOrder table) := by
    simp [rows, List.map_map, Function.comp_def]
  have rowTails : rows.map (fun row => row.2.2) = node.parentOrders.flatten.map (cachedParentTail table) := by
    simp [rows, List.map_map, Function.comp_def]
  let evidence : NodeCertified node.name (rows.map (fun row => row.2.1) ++ node.parentOrders)
      (rows.map (fun row => row.2.2)) := rowTails.symm ▸ (congrArg (· ++ node.parentOrders) rowOrders.symm) ▸ original
  have evidenceOutputs := cast_node_outputs (congrArg (· ++ node.parentOrders) rowOrders.symm) rowTails.symm original
  have outputSame : evidence.output = certificate.output :=
    evidenceOutputs.1.trans (originalOutput.trans (normalizedOutputs.1.trans (restoredOutput.trans filteredOutputs.1)))
  have tailSame : evidence.selection.output = certificate.selection.output :=
    evidenceOutputs.2.trans (originalTail.trans (normalizedOutputs.2.trans (restoredTail.trans filteredOutputs.2)))
  have parentsAvailable := collectParents_success_iff.mp ⟨entries, collected⟩
  have derivation : GraphTrace graph node.name evidence.output
      (if node.suffix then evidence.output else evidence.selection.output) :=
    GraphTrace.node found rows (by simp [rows, List.map_map, Function.comp_def]) (by
      intro row member
      obtain ⟨name, present, same⟩ := List.mem_map.mp member
      subst row
      obtain ⟨entry, cached⟩ := parentsAvailable name present
      simpa [cachedOrder, cachedParentTail, cached] using valid.tail name entry cached) evidence
  simpa only [outputSame, tailSame] using derivation

/-- Successful checked node execution is graph-sound under canonical parent
metadata, without a supplied root GraphTrace or caller node certificate. -/
theorem computeNode_checked_graph_sound (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (success : computeNode table node true = .ok result) :
    GraphTrace graph node.name result.precedence
      (if node.suffix then result.precedence else selectedTail table result.inheritedSuffix) := by
  obtain ⟨entries, chosen, tails, certificate, collected, _, tailsFound, claimed, same⟩ :=
    computeNode_checked_evidence success
  have actualTails := collectSuffixTails_complete (collected_suffix_available valid collected)
  have tailIndices : tails = suffixTails table (entries.map (·.mostSpecificSuffix)) :=
    Except.ok.inj (tailsFound.symm.trans actualTails)
  let canonical := tailIndices ▸ certificate
  have outputs := cast_node_outputs rfl tailIndices certificate
  have derivation := checked_certificate_graph valid found collected canonical
  subst result
  dsimp only [canonical] at derivation
  simpa only [outputs.1, outputs.2, claimed] using derivation

/-- Actual fresh checked insertion establishes full graph-backed metadata from
success itself. The root derivation is extracted, not assumed. -/
theorem computeNode_checked_insert_sound (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node) (fresh : lookup table node.name = none)
    (success : computeNode table node true = .ok result) :
    MetadataInvariant graph (table.insert node.name result) := by
  have derivation := computeNode_checked_graph_sound valid found success
  obtain ⟨entries, _, _, _, collected, _⟩ := computeNode_checked_evidence success
  obtain ⟨actual, computed, _, inserted⟩ := computeNode_metadata_insert valid derivation found fresh collected true
  have same := Except.ok.inj (computed.symm.trans success)
  simpa only [same] using inserted

end LeanPoo.C4.LinearizeState
