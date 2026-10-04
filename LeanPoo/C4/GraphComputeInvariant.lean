import LeanPoo.C4.ComputeInvariant

namespace LeanPoo.C4.LinearizeState

/-- Complete canonical parent-tail projection, including empty graph tails. -/
def cachedParentTail (table : Table) (name : String) : List String :=
  ((lookup table name).map (fun entry => selectedTail table entry.mostSpecificSuffix)).getD []

theorem collected_parent_tail_map (collected : collectParents table names = .ok entries) :
    entries.map (fun entry => selectedTail table entry.mostSpecificSuffix) =
      names.map (cachedParentTail table) := by
  have aligned := collectParents_sound collected
  clear collected
  induction aligned with
  | nil => rfl
  | cons found rest ih => simp [cachedParentTail, found, ih]

private theorem cast_node_outputs (ordersSame : orders = otherOrders) (tailsSame : tails = otherTails)
    (certificate : NodeCertified name orders tails) :
    (tailsSame ▸ ordersSame ▸ certificate : NodeCertified name otherOrders otherTails).output = certificate.output ∧
      (tailsSame ▸ ordersSame ▸ certificate : NodeCertified name otherOrders otherTails).selection.output =
        certificate.selection.output := by
  cases ordersSame; cases tailsSame; exact ⟨rfl, rfl⟩

/-- Original graph rows systematically supply the exact normalized node
certificate used by computeNode. No caller-supplied node certificate is needed. -/
theorem graph_node_certificate (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) :
    ∃ certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))),
      certificate.output = output ∧
        tail = (if node.suffix then certificate.output else certificate.selection.output) ∧
        ∀ target declaration, graph.findNode? target = some declaration → declaration.suffix = true →
          Ancestor graph target node.name → target ≠ node.name → target ∈ certificate.selection.output := by
  obtain ⟨rows, names, rowCache, original, outputSame, tailSame⟩ :=
    cached_graph_rows valid.toCacheInvariant trace found collected
  have rowOrders : rows.map (fun row => row.2.1) = node.parentOrders.flatten.map (cachedOrder table) := by
    rw [← names, List.map_map]
    apply List.map_congr_left
    intro row member
    obtain ⟨entry, _, cached, same, _⟩ := rowCache row member
    simp only [Function.comp_apply, cachedOrder, cached, Option.map_some, Option.getD_some]
    exact same.symm
  have rowTails : rows.map (fun row => row.2.2) = node.parentOrders.flatten.map (cachedParentTail table) := by
    rw [← names, List.map_map]
    apply List.map_congr_left
    intro row member
    obtain ⟨entry, _, cached, _, parentTrace⟩ := rowCache row member
    have same := (parentTrace.unique (valid.tail row.1 entry cached)).2
    simp only [Function.comp_apply, cachedParentTail, cached, Option.map_some, Option.getD_some]
    exact same
  let aligned : NodeCertified node.name
      (node.parentOrders.flatten.map (cachedOrder table) ++ node.parentOrders)
      (node.parentOrders.flatten.map (cachedParentTail table)) :=
    rowTails ▸ (congrArg (· ++ node.parentOrders) rowOrders) ▸ original
  have alignedOutputs := cast_node_outputs (congrArg (· ++ node.parentOrders) rowOrders) rowTails original
  obtain ⟨normalized, normalizedOutput, normalizedTail⟩ := nodeCertificate_normalize aligned
  obtain ⟨cleaned, cleanedOutput, cleanedTail⟩ := normalized.drop_empty
  have parentOrders : (unique node.parentOrders.flatten).map (cachedOrder table) = entries.map (·.precedence) :=
    (collected_precedence_map collected).symm
  have parentTails : (unique node.parentOrders.flatten).map (cachedParentTail table) =
      entries.map (fun entry => selectedTail table entry.mostSpecificSuffix) :=
    (collected_parent_tail_map collected).symm
  have runtimeTails :
      ((unique node.parentOrders.flatten).map (cachedParentTail table)).filter (fun tail => !tail.isEmpty) =
        suffixTails table (entries.map (·.mostSpecificSuffix)) := by
    rw [parentTails, suffixTails_drop_empty valid.suffixes (collected_suffix_available valid collected)]
    simp only [List.map_map, Function.comp_def]
  let certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))) :=
    runtimeTails ▸ (congrArg (· ++ MergeState.pending node.parentOrders) parentOrders) ▸ cleaned
  have certificateOutputs := cast_node_outputs
    (congrArg (· ++ MergeState.pending node.parentOrders) parentOrders) runtimeTails cleaned
  have outputEq : certificate.output = output :=
    certificateOutputs.1.trans (cleanedOutput.trans (normalizedOutput.trans (alignedOutputs.1.trans outputSame.symm)))
  have selectionEq : certificate.selection.output = original.selection.output :=
    certificateOutputs.2.trans (cleanedTail.trans (normalizedTail.trans alignedOutputs.2))
  refine ⟨certificate, outputEq, by simpa [outputEq, selectionEq, ← outputSame] using tailSame, ?_⟩
  intro target declaration targetFound marked ancestor proper
  rw [selectionEq]
  cases ancestor with
  | self => exact False.elim (proper rfl)
  | parent actual member earlier =>
    have same := Option.some.inj (actual.symm.trans found)
    rw [same, ← names] at member
    obtain ⟨row, present, rowName⟩ := List.mem_map.mp member
    obtain ⟨_, _, _, _, parentTrace⟩ := rowCache row present
    have earlier' : Ancestor graph target row.1 := by simpa only [rowName] using earlier
    obtain ⟨targetOutput, targetTail, targetTrace, inherited⟩ := parentTrace.ancestor_tail earlier'
    have whole := targetTrace.flagged targetFound marked
    have targetMember : target ∈ row.2.2 := by
      rw [whole] at inherited
      exact inherited.sublist.subset targetTrace.root_mem
    exact (original.selection.containsTail row.2.2
      (List.mem_map.mpr ⟨row, present, rfl⟩)).sublist.subset targetMember

/-- Both actual node modes reproduce an original finite graph derivation,
given graph-backed parent metadata and successful parent collection. -/
theorem computeNode_graph_complete (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool) :
    ∃ chosen, computeNode table node checked = .ok {
      precedence := output
      inheritedSuffix := chosen
      mostSpecificSuffix := if node.suffix then some node.name else chosen } ∧
      tail = (if node.suffix then output else selectedTail table chosen) := by
  obtain ⟨certificate, outputSame, tailSame, _⟩ := graph_node_certificate valid trace found collected
  obtain ⟨chosen, _, computed, selectedSame⟩ := computeNode_certified valid trace found collected certificate checked
  exact ⟨chosen, by simpa [outputSame] using computed,
    by simpa [outputSame, ← selectedSame] using tailSame⟩

/-- Actual fresh insertion preserves graph provenance and literal links
without any externally supplied normalized node certificate. -/
theorem computeNode_graph_insert (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool) :
    ∃ result, computeNode table node checked = .ok result ∧ result.precedence = output ∧
      CacheInvariant graph (table.insert node.name result) := by
  obtain ⟨certificate, same, _, _⟩ := graph_node_certificate valid trace found collected
  have derived : GraphTrace graph node.name certificate.output tail := by simpa [same] using trace
  obtain ⟨result, computed, invariant⟩ :=
    computeNode_insert_preserves valid found fresh collected certificate derived checked
  obtain ⟨chosen, expected, _⟩ := computeNode_graph_complete valid trace found collected checked
  have identical := Except.ok.inj (computed.symm.trans expected)
  exact ⟨result, computed, by rw [identical], invariant⟩

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

theorem fresh_insert_retains (fresh : lookup table name = none)
    (found : lookup table query = some child) : lookup (table.insert name entry) query = some child := by
  have different : name ≠ query := by
    intro same; subst query; rw [fresh] at found; cases found
  simp [lookup_insert, different, found]

theorem selectedTail_fresh_insert (fresh : lookup table name = none)
    (available : ∀ suffix, source = some suffix → ∃ child, lookup table suffix = some child) :
    selectedTail (table.insert name entry) source = selectedTail table source := by
  cases source with
  | none => rfl
  | some suffix =>
    obtain ⟨child, found⟩ := available suffix rfl
    simp [selectedTail, found, fresh_insert_retains fresh found]

/-- Fresh insertion preserves all existing semantic metadata, requiring only
the new entry's graph tail, actual selected cache, and graph coverage evidence. -/
theorem MetadataInvariant.insert {tail : List String} (valid : MetadataInvariant graph table)
    (fresh : lookup table name = none) (trace : GraphTrace graph name entry.precedence tail)
    (links : ∀ next, entry.inheritedSuffix = some next →
      ∃ child, lookup table next = some child ∧ child.precedence.IsSuffix entry.precedence.tail)
    (tailTrace : GraphTrace graph name entry.precedence
      (selectedTail (table.insert name entry) entry.mostSpecificSuffix))
    (selected : ∀ suffix, entry.mostSpecificSuffix = some suffix →
      ∃ child, lookup (table.insert name entry) suffix = some child)
    (coverage : ∀ target node, graph.findNode? target = some node → node.suffix = true →
      Ancestor graph target name → target ≠ name → ∃ next child,
        entry.inheritedSuffix = some next ∧ lookup (table.insert name entry) next = some child ∧
          target ∈ child.precedence) : MetadataInvariant graph (table.insert name entry) := by
  refine ⟨valid.toCacheInvariant.insert fresh trace links, ?_, ?_, ?_⟩
  · intro query cached found
    by_cases same : name = query
    · subst query
      have identical : entry = cached := by simpa [lookup_insert] using found
      subst cached; exact tailTrace
    · have original : lookup table query = some cached := by simpa [lookup_insert, same] using found
      rw [selectedTail_fresh_insert fresh (valid.selected query cached original)]
      exact valid.tail query cached original
  · intro query cached found suffix choice
    by_cases same : name = query
    · subst query
      have identical : entry = cached := by simpa [lookup_insert] using found
      subst cached; exact selected suffix choice
    · have original : lookup table query = some cached := by simpa [lookup_insert, same] using found
      obtain ⟨child, childFound⟩ := valid.selected query cached original suffix choice
      exact ⟨child, fresh_insert_retains fresh childFound⟩
  · intro query cached found target node declared marked ancestor proper
    by_cases same : name = query
    · subst query
      have identical : entry = cached := by simpa [lookup_insert] using found
      subst cached; exact coverage target node declared marked ancestor proper
    · have original : lookup table query = some cached := by simpa [lookup_insert, same] using found
      obtain ⟨next, child, link, childFound, member⟩ :=
        valid.coverage query cached original target node declared marked ancestor proper
      exact ⟨next, child, link, fresh_insert_retains fresh childFound, member⟩

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

/-- Actual graph-derived node computation establishes the stronger metadata
invariant after fresh insertion, including proper marked-ancestor coverage. -/
theorem computeNode_metadata_insert (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool) :
    ∃ result, computeNode table node checked = .ok result ∧ result.precedence = output ∧
      MetadataInvariant graph (table.insert node.name result) := by
  obtain ⟨certificate, outputSame, tailSame, covers⟩ := graph_node_certificate valid trace found collected
  obtain ⟨chosen, selected, computed, sameTail⟩ :=
    computeNode_certified valid trace found collected certificate checked
  let result : Linearization := {
    precedence := certificate.output
    inheritedSuffix := chosen
    mostSpecificSuffix := if node.suffix then some node.name else chosen }
  have chosenAvailable : ∀ suffix, chosen = some suffix → ∃ child, lookup table suffix = some child := by
    intro suffix choice
    rw [choice] at selected
    rcases (selectSuffix_sound selected).1 with impossible | member
    · cases impossible
    · exact collected_suffix_available valid collected suffix member
  have derived : GraphTrace graph node.name certificate.output tail := by simpa [outputSame] using trace
  have unchanged : selectedTail (table.insert node.name result) chosen = selectedTail table chosen :=
    selectedTail_fresh_insert fresh chosenAvailable
  refine ⟨result, computed, outputSame, valid.insert fresh derived ?_ ?_ ?_ ?_⟩
  · intro next link
    have choice : chosen = some next := link
    obtain ⟨child, cached⟩ := chosenAvailable next choice
    have precedence : certificate.selection.output = child.precedence := by
      simpa [selectedTail, choice, cached] using sameTail.symm
    exact ⟨child, cached, by simpa [result, NodeCertified.output, precedence] using certificate.ancestry.suffix⟩
  · rw [tailSame] at derived
    cases marked : node.suffix with
    | false =>
      change GraphTrace graph node.name certificate.output
        (selectedTail (table.insert node.name result) result.mostSpecificSuffix)
      have choice : result.mostSpecificSuffix = chosen := by simp [result, marked]
      rw [choice, unchanged, sameTail]
      simpa only [marked, Bool.false_eq_true, ↓reduceIte] using derived
    | true =>
      simpa [result, marked, selectedTail, lookup_insert] using derived
  · intro suffix choice
    by_cases marked : node.suffix = true
    · have nameSame : node.name = suffix := by simpa [result, marked] using choice
      subst suffix
      exact ⟨result, by simp [lookup_insert]⟩
    · have oldChoice : chosen = some suffix := by simpa [result, marked] using choice
      obtain ⟨child, cached⟩ := chosenAvailable suffix oldChoice
      exact ⟨child, fresh_insert_retains fresh cached⟩
  · intro target declaration declared marked ancestor proper
    have member : target ∈ selectedTail table chosen := by
      rw [sameTail]; exact covers target declaration declared marked ancestor proper
    cases choice : chosen with
    | none => simp [selectedTail, choice] at member
    | some next =>
      obtain ⟨child, cached⟩ := chosenAvailable next choice
      refine ⟨next, child, by simp [result, choice], fresh_insert_retains fresh cached, ?_⟩
      simpa [selectedTail, choice, cached] using member

end LeanPoo.C4.LinearizeState
