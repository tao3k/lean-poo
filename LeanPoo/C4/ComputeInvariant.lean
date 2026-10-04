import LeanPoo.C4.MetadataInvariant

namespace LeanPoo.C4

/-- Omitting empty parent tails preserves independent tail certification. -/
theorem TailCertified.drop_empty (certificate : TailCertified tails) :
    ∃ normalized : TailCertified (tails.filter (fun tail => !tail.isEmpty)),
      normalized.output = certificate.output := by
  refine ⟨⟨certificate.output, ?_, ?_⟩, rfl⟩
  · by_cases empty : certificate.output = []
    · refine .inl ⟨List.filter_eq_nil_iff.mpr ?_, empty⟩
      intro tail member
      have kept := certificate.containsTail tail member
      rw [empty] at kept
      have same : tail = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero kept.length_le)
      simp [same]
    · rcases certificate.chosen with ⟨_, same⟩ | member
      · exact False.elim (empty same)
      · exact .inr (List.mem_filter.mpr ⟨member, by simpa using empty⟩)
  · intro tail member
    exact certificate.containsTail tail (List.mem_filter.mp member).1

private theorem suffix_cast_output (same : left = right) (certificate : SuffixCertified orders left) :
    (same ▸ certificate : SuffixCertified orders right).output = certificate.output := by
  cases same; rfl

/-- The complete node certificate survives omission of empty parent tails. -/
theorem NodeCertified.drop_empty (certificate : NodeCertified name orders tails) :
    ∃ normalized : NodeCertified name orders (tails.filter (fun tail => !tail.isEmpty)),
      normalized.output = certificate.output ∧
        normalized.selection.output = certificate.selection.output := by
  obtain ⟨selection, same⟩ := certificate.selection.drop_empty
  let ancestry : SuffixCertified orders selection.output := same.symm ▸ certificate.ancestry
  have output : ancestry.output = certificate.ancestry.output := suffix_cast_output same.symm _
  have unique : selection.output.Nodup := by rw [same]; exact certificate.tailUnique
  have fresh : name ∉ ancestry.output := by rw [output]; exact certificate.fresh
  exact ⟨⟨selection, ancestry, unique, fresh⟩, by simp [NodeCertified.output, output], same⟩

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

/-- Read the actual selected cache entry rather than trusting a default projection. -/
theorem readSuffix_complete
    (available : ∀ name, selected = some name → ∃ entry, lookup table name = some entry) :
    readSuffix table selected = .ok (selectedTail table selected) := by
  cases selected with
  | none => rfl
  | some name =>
    obtain ⟨entry, found⟩ := available name rfl
    simp [readSuffix, selectedTail, found, pure, Except.pure]

private theorem collectSuffixTailsRev_complete
    (available : ∀ name, some name ∈ sources → ∃ entry, lookup table name = some entry)
    (reversed : List (List String)) :
    collectSuffixTailsRev table sources reversed = .ok ((suffixTails table sources).reverse ++ reversed) := by
  induction sources generalizing reversed with
  | nil => rfl
  | cons source rest ih =>
    have remaining := ih (fun name member => available name (List.mem_cons_of_mem source member))
    cases source with
    | none => simpa [collectSuffixTailsRev, suffixTails] using remaining reversed
    | some name =>
      obtain ⟨entry, found⟩ := available name List.mem_cons_self
      simp [collectSuffixTailsRev, readSuffix, found, remaining, suffixTails,
        List.reverse_cons, List.append_assoc, bind, Except.bind, pure, Except.pure]

theorem collectSuffixTails_complete
    (available : ∀ name, some name ∈ sources → ∃ entry, lookup table name = some entry) :
    collectSuffixTails table sources = .ok (suffixTails table sources) := by
  simp [collectSuffixTails, collectSuffixTailsRev_complete available [], bind, Except.bind, pure, Except.pure]

/-- Actual node computation in either mode reproduces supplied complete
normalized node evidence, once its collected and selected input stages agree. -/
theorem computeNode_complete
    (collected : collectParents table (parents node) = .ok entries)
    (selected : selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen)
    (available : ∀ name, some name ∈ entries.map (·.mostSpecificSuffix) →
      ∃ entry, lookup table name = some entry)
    (certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))))
    (tailMatches : certificate.selection.output = selectedTail table chosen) (checked : Bool) :
    computeNode table node checked = .ok {
      precedence := certificate.output
      inheritedSuffix := chosen
      mostSpecificSuffix := if node.suffix then some node.name else chosen } := by
  have chosenAvailable : ∀ name, chosen = some name → ∃ entry, lookup table name = some entry := by
    intro name same
    rw [same] at selected
    rcases (selectSuffix_sound selected).1 with impossible | member
    · cases impossible
    · exact available name member
  have read := readSuffix_complete chosenAvailable
  have tails := collectSuffixTails_complete available
  have localAccepted : (MergeState.pending node.parentOrders).all
      (fun order => respectsSuffixTail order (selectedTail table chosen)) = true := by
    apply List.all_eq_true.mpr
    intro order member
    rw [← tailMatches]
    exact respectsSuffixTail_complete
      (certificate.ancestry.compatible order (List.mem_append_right _ member)) certificate.tailUnique
  have raw := MergeState.merge_complete certificate.ancestry.trace
  have cleaned : merge (entries.map (fun result => withoutTail result.precedence (selectedTail table chosen)) ++
      (MergeState.pending node.parentOrders).map (fun order => withoutTail order (selectedTail table chosen))) =
      .ok certificate.ancestry.front := by
    simpa only [tailMatches, List.map_append, List.map_map, Function.comp_def] using raw
  obtain ⟨certified, certifiedOk, output, _⟩ := certifyNode_complete certificate
  have ancestryOutput : certified.ancestry.output = certificate.ancestry.output :=
    List.cons.inj output |>.2
  have accepted' : (node.parentOrders.filter (fun order => !order.isEmpty)).all
      (fun order => respectsSuffixTail order (selectedTail table chosen)) = true := localAccepted
  have cleaned' : merge (entries.map (fun result => withoutTail result.precedence (selectedTail table chosen)) ++
      (node.parentOrders.filter (fun order => !order.isEmpty)).map
        (fun order => withoutTail order (selectedTail table chosen))) = .ok certificate.ancestry.front := cleaned
  have certifiedOk' : certifyNode node.name
      (entries.map (·.precedence) ++ node.parentOrders.filter (fun order => !order.isEmpty))
      (suffixTails table (entries.map (·.mostSpecificSuffix))) (selectedTail table chosen) = .ok certified := by
    rw [← tailMatches]; exact certifiedOk
  cases checked <;>
    simp only [computeNode, collected, selected, read, accepted', Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, tails, certifiedOk', cleaned',
      bind, Except.bind, pure, Except.pure]
  all_goals simp only [NodeCertified.output, SuffixCertified.output, tailMatches]
  have combined : certified.ancestry.front ++ certified.selection.output =
      certificate.ancestry.front ++ selectedTail table chosen := by
    simpa only [SuffixCertified.output, tailMatches] using ancestryOutput
  rw [combined]

/-- Successful collection plus canonical metadata guarantees every supplied
nonempty suffix name has an actual cache entry. -/
theorem collected_suffix_available (valid : MetadataInvariant graph table)
    (collected : collectParents table names = .ok entries) :
    ∀ name, some name ∈ entries.map (·.mostSpecificSuffix) → ∃ entry, lookup table name = some entry := by
  have aligned := collectParents_sound collected
  clear collected
  induction aligned with
  | nil => simp
  | cons found rest ih =>
    intro suffix member
    rcases List.mem_cons.mp (by simpa only [List.map_cons] using member) with same | member
    · exact valid.selected _ _ found suffix same.symm
    · exact ih suffix member

/-- Runtime omission of absent suffix metadata is exactly empty-tail deletion
on the complete cached tail projection. Cached suffix precedences are nonempty. -/
theorem suffixTails_drop_empty (valid : SuffixCacheInvariant table)
    (available : ∀ name, some name ∈ sources → ∃ entry, lookup table name = some entry) :
    suffixTails table sources = (sources.map (selectedTail table)).filter (fun tail => !tail.isEmpty) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    have remaining := ih (fun name member => available name (List.mem_cons_of_mem source member))
    cases source with
    | none => simpa [suffixTails, selectedTail] using remaining
    | some name =>
      obtain ⟨entry, found⟩ := available name List.mem_cons_self
      have head := valid.head name entry found
      have nonempty : entry.precedence.isEmpty = false := by
        cases actual : entry.precedence with
        | nil => simp [actual] at head
        | cons first rest => rfl
      simp [suffixTails, selectedTail, found, nonempty]
      simpa [suffixTails] using remaining

/-- Graph-backed metadata derives the actual selection and matching tail,
then both computeNode modes reproduce complete normalized node evidence.
No successful computeNode result is a premise of this theorem. -/
theorem computeNode_certified (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries)
    (certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix)))) (checked : Bool) :
    ∃ chosen, selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen ∧
      computeNode table node checked = .ok {
      precedence := certificate.output
      inheritedSuffix := chosen
      mostSpecificSuffix := if node.suffix then some node.name else chosen } ∧
      selectedTail table chosen = certificate.selection.output := by
  obtain ⟨chosen, selected⟩ := collected_suffix_selection_complete valid trace found collected
  obtain ⟨selection, same⟩ := collected_suffix_selection_certified valid collected selected
  have tailMatches := (certificate.selection.unique selection).trans same
  exact ⟨chosen, selected, computeNode_complete collected selected
    (collected_suffix_available valid collected) certificate tailMatches checked, tailMatches.symm⟩

/-- Actual computed-node insertion preserves the original graph provenance
and literal suffix-link invariant once the supplied node evidence has its
graph derivation. Strong metadata coverage population remains separate. -/
theorem computeNode_insert_preserves (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none)
    (collected : collectParents table (parents node) = .ok entries)
    (certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))))
    (trace : GraphTrace graph node.name certificate.output tail) (checked : Bool) :
    ∃ result, computeNode table node checked = .ok result ∧
      CacheInvariant graph (table.insert node.name result) := by
  obtain ⟨chosen, selected, computed, sameTail⟩ :=
    computeNode_certified valid trace found collected certificate checked
  let result : Linearization := {
    precedence := certificate.output
    inheritedSuffix := chosen
    mostSpecificSuffix := if node.suffix then some node.name else chosen }
  refine ⟨result, computed, valid.toCacheInvariant.insert fresh trace ?_⟩
  intro next link
  have chosenName : chosen = some next := link
  rw [chosenName] at selected
  have member : some next ∈ entries.map (·.mostSpecificSuffix) := by
    rcases (selectSuffix_sound selected).1 with impossible | member
    · cases impossible
    · exact member
  obtain ⟨child, cached⟩ := collected_suffix_available valid collected next member
  have precedence : certificate.selection.output = child.precedence := by
    simpa [selectedTail, chosenName, cached] using sameTail.symm
  refine ⟨child, cached, ?_⟩
  simpa [result, NodeCertified.output, precedence] using certificate.ancestry.suffix

end LeanPoo.C4.LinearizeState
