import LeanPoo.C4.SelectionInvariant
import Std.Data.HashSet.Lemmas

namespace LeanPoo.C4

/-- Positional relation between equally long source and result lists. -/
inductive ListAligned (R : α → β → Prop) : List α → List β → Prop where
  | nil : ListAligned R [] []
  | cons : R name entry → ListAligned R names entries →
      ListAligned R (name :: names) (entry :: entries)

theorem ListAligned.length_eq (aligned : ListAligned R names entries) :
    names.length = entries.length := by
  induction aligned with
  | nil => rfl
  | cons related aligned ih => simpa using ih

/-- Declarative first-occurrence specification with an explicit seen set. -/
def firstOccurrences (seen : Std.HashSet String) : List String → List String
  | [] => []
  | name :: rest =>
    if seen.contains name then firstOccurrences seen rest
    else name :: firstOccurrences (seen.insert name) rest

private theorem unique_fold (items : List String) (seen : Std.HashSet String)
    (reversed : List String) :
    (items.foldl uniqueStep (seen, reversed)).2.reverse =
      reversed.reverse ++ firstOccurrences seen items := by
  induction items generalizing seen reversed with
  | nil => simp [firstOccurrences]
  | cons name rest ih =>
    by_cases present : seen.contains name = true
    · simp [List.foldl_cons, uniqueStep, firstOccurrences, present, ih]
    · simp [List.foldl_cons, uniqueStep, firstOccurrences, present, ih, List.append_assoc]

/-- The actual HashSet fold retains first occurrences, in their original order. -/
theorem unique_firstOccurrences (items : List String) :
    unique items = firstOccurrences {} items := by
  simpa [unique] using unique_fold items {} []

private theorem firstOccurrences_mem (items : List String) (seen : Std.HashSet String) :
    name ∈ firstOccurrences seen items ↔ name ∈ items ∧ seen.contains name = false := by
  induction items generalizing seen with
  | nil => simp [firstOccurrences]
  | cons head rest ih =>
    by_cases present : seen.contains head = true
    · simp only [firstOccurrences, present, ↓reduceIte, ih, List.mem_cons]
      constructor
      · rintro ⟨member, absent⟩; exact ⟨.inr member, absent⟩
      · rintro ⟨same | member, absent⟩
        · subst name; simp [present] at absent
        · exact ⟨member, absent⟩
    · have absent : seen.contains head = false := Bool.eq_false_iff.mpr present
      simp only [firstOccurrences, absent, Bool.false_eq_true, ↓reduceIte, List.mem_cons, ih,
        Std.HashSet.contains_insert]
      by_cases same : name = head
      · subst name; simp [absent]
      · simp [same, Ne.symm same]

private theorem firstOccurrences_nodup (items : List String) (seen : Std.HashSet String) :
    (firstOccurrences seen items).Nodup := by
  induction items generalizing seen with
  | nil => simp [firstOccurrences]
  | cons name rest ih =>
    by_cases present : seen.contains name = true
    · simpa [firstOccurrences, present] using ih seen
    · simp only [firstOccurrences, present]
      apply List.nodup_cons.mpr
      exact ⟨by simp [firstOccurrences_mem], ih (seen.insert name)⟩

private theorem firstOccurrences_sublist (items : List String) (seen : Std.HashSet String) :
    (firstOccurrences seen items).Sublist items := by
  induction items generalizing seen with
  | nil => exact .refl _
  | cons name rest ih =>
    by_cases present : seen.contains name = true
    · simpa [firstOccurrences, present] using (ih seen).cons name
    · simpa [firstOccurrences, present] using (ih (seen.insert name)).cons_cons name

theorem unique_mem : name ∈ unique items ↔ name ∈ items := by
  rw [unique_firstOccurrences, firstOccurrences_mem]
  simp

theorem unique_nodup (items : List String) : (unique items).Nodup := by
  rw [unique_firstOccurrences]
  exact firstOccurrences_nodup items {}

theorem unique_sublist (items : List String) : (unique items).Sublist items := by
  rw [unique_firstOccurrences]
  exact firstOccurrences_sublist items {}

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

theorem parents_mem : name ∈ parents node ↔ name ∈ node.parentOrders.flatten := unique_mem

theorem parents_nodup (node : Node) : (parents node).Nodup := unique_nodup _

theorem parents_sublist (node : Node) : (parents node).Sublist node.parentOrders.flatten :=
  unique_sublist _

private theorem collectParentsRev_complete
    (aligned : ListAligned (fun name entry => lookup table name = some entry) names entries)
    (reversed : List Linearization) :
    collectParentsRev table names reversed = .ok (entries.reverse ++ reversed) := by
  induction aligned generalizing reversed with
  | nil => rfl
  | cons found aligned ih =>
    simp [collectParentsRev, found, ih, List.reverse_cons, List.append_assoc]

/-- Every cached lookup is collected exactly once per supplied name and in
that name's position. This lemma also permits repeated names. -/
theorem collectParents_complete
    (aligned : ListAligned (fun name entry => lookup table name = some entry) names entries) :
    collectParents table names = .ok entries := by
  simp [collectParents, collectParentsRev_complete aligned [], bind, Except.bind, pure, Except.pure]

private theorem collectParentsRev_sound
    (success : collectParentsRev table names reversed = .ok result) :
    ∃ entries, ListAligned (fun name entry => lookup table name = some entry) names entries ∧
      result = entries.reverse ++ reversed := by
  induction names generalizing reversed result with
  | nil =>
    simp only [collectParentsRev, Except.ok.injEq] at success
    exact ⟨[], .nil, success.symm⟩
  | cons name rest ih =>
    cases found : lookup table name with
    | none => simp [collectParentsRev, found, throw] at success
    | some entry =>
      have remaining : collectParentsRev table rest (entry :: reversed) = .ok result := by
        simpa [collectParentsRev, found, bind, Except.bind] using success
      obtain ⟨entries, aligned, same⟩ := ih remaining
      exact ⟨entry :: entries, .cons found aligned,
        by simpa [List.reverse_cons, List.append_assoc] using same⟩

/-- Successful collection has exact positional cache provenance. -/
theorem collectParents_sound (success : collectParents table names = .ok entries) :
    ListAligned (fun name entry => lookup table name = some entry) names entries := by
  cases result : collectParentsRev table names [] with
  | error error => simp [collectParents, result, bind, Except.bind] at success
  | ok reversed =>
    have same : reversed.reverse = entries := by
      simpa [collectParents, result, bind, Except.bind, pure, Except.pure] using success
    obtain ⟨actual, aligned, equal⟩ := collectParentsRev_sound result
    have outputs : actual = entries := by simpa [equal] using same
    simpa [outputs] using aligned

theorem collectParents_length (success : collectParents table names = .ok entries) :
    entries.length = names.length := (collectParents_sound success).length_eq.symm

private theorem aligned_available
    (available : ∀ name ∈ names, ∃ entry, lookup table name = some entry) :
    ∃ entries, ListAligned (fun name entry => lookup table name = some entry) names entries := by
  induction names with
  | nil => exact ⟨[], .nil⟩
  | cons name rest ih =>
    obtain ⟨entry, found⟩ := available name List.mem_cons_self
    obtain ⟨entries, aligned⟩ := ih (fun next member =>
      available next (List.mem_cons_of_mem name member))
    exact ⟨entry :: entries, .cons found aligned⟩

private theorem aligned_left_member {R : α → β → Prop}
    (aligned : ListAligned R names entries) (member : name ∈ names) :
    ∃ entry ∈ entries, R name entry := by
  induction aligned with
  | nil => simp at member
  | cons related aligned ih =>
    rcases List.mem_cons.mp member with same | present
    · subst name; exact ⟨_, List.mem_cons_self, related⟩
    · obtain ⟨entry, present, related⟩ := ih present
      exact ⟨entry, List.mem_cons_of_mem _ present, related⟩

private theorem aligned_right_member {R : α → β → Prop}
    (aligned : ListAligned R names entries) (member : entry ∈ entries) :
    ∃ name ∈ names, R name entry := by
  induction aligned with
  | nil => simp at member
  | cons related aligned ih =>
    rcases List.mem_cons.mp member with same | present
    · subst entry; exact ⟨_, List.mem_cons_self, related⟩
    · obtain ⟨name, present, related⟩ := ih present
      exact ⟨name, List.mem_cons_of_mem _ present, related⟩

/-- Deduplicated collection succeeds exactly when all declared parent names
have cached results; repeats and empty local orders add no lookup obligations. -/
theorem collectParents_success_iff :
    (∃ entries, collectParents table (parents node) = .ok entries) ↔
      ∀ name ∈ node.parentOrders.flatten, ∃ entry, lookup table name = some entry := by
  constructor
  · rintro ⟨entries, success⟩ name member
    obtain ⟨entry, _, found⟩ := aligned_left_member (collectParents_sound success)
      (parents_mem.mpr member)
    exact ⟨entry, found⟩
  · intro available
    obtain ⟨entries, aligned⟩ := aligned_available (fun name member =>
      available name (parents_mem.mp member))
    exact ⟨entries, collectParents_complete aligned⟩

/-- Every fetched parent precedence agrees with the original graph derivation
and is retained as an ordered sublist of the complete node output. -/
theorem collected_parent_preserves (valid : CacheInvariant graph table)
    (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (success : collectParents table (parents node) = .ok entries) (member : entry ∈ entries) :
    ∃ name ∈ node.parentOrders.flatten, ∃ parentTail,
      lookup table name = some entry ∧ GraphTrace graph name entry.precedence parentTail ∧
      entry.precedence.Sublist output := by
  obtain ⟨name, present, cached⟩ := aligned_right_member (collectParents_sound success) member
  have declared := parents_mem.mp present
  obtain ⟨parentOutput, parentTail, parentTrace, kept⟩ := trace.parent found declared
  obtain ⟨cachedTail, cachedTrace⟩ := valid.derived name entry cached
  have same := (parentTrace.unique cachedTrace).1
  exact ⟨name, declared, parentTail, cached, by simpa [same] using parentTrace,
    by simpa [same] using kept⟩

/-- Original graph rows, including every repeated declared edge, agree with
cached parent precedences. The original full node certificate remains attached.
This does not yet prove duplicate candidate removal preserves merge choices. -/
theorem cached_graph_rows (valid : CacheInvariant graph table)
    (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (success : collectParents table (parents node) = .ok entries) :
    ∃ rows : List (String × (List String × List String)),
      rows.map Prod.fst = node.parentOrders.flatten ∧
      (∀ row ∈ rows, ∃ entry ∈ entries, lookup table row.1 = some entry ∧
        entry.precedence = row.2.1 ∧ GraphTrace graph row.1 row.2.1 row.2.2) ∧
      ∃ certificate : NodeCertified node.name
        (rows.map (fun row => row.2.1) ++ node.parentOrders) (rows.map (fun row => row.2.2)),
        output = certificate.output ∧
          tail = (if node.suffix then certificate.output else certificate.selection.output) := by
  cases trace with
  | node actual rows names parentTraces certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    refine ⟨rows, names, ?_, certificate, rfl, rfl⟩
    intro row member
    have declared : row.1 ∈ rows.map Prod.fst := List.mem_map.mpr ⟨row, member, rfl⟩
    rw [names] at declared
    obtain ⟨entry, present, cached⟩ := aligned_left_member (collectParents_sound success)
      (parents_mem.mpr declared)
    obtain ⟨cachedTail, cachedTrace⟩ := valid.derived row.1 entry cached
    exact ⟨entry, present, cached, (cachedTrace.unique (parentTraces row member)).1,
      parentTraces row member⟩

end LeanPoo.C4.LinearizeState
