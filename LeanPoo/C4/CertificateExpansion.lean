import LeanPoo.C4.ExecutionInvariant

namespace LeanPoo.C4

/-- Restore omitted empty tails, including the all-empty nonempty input case. -/
theorem TailCertified.restore_empty
    (certificate : TailCertified (tails.filter (fun tail => !tail.isEmpty))) :
    ∃ original : TailCertified tails, original.output = certificate.output := by
  refine ⟨⟨certificate.output, ?_, ?_⟩, rfl⟩
  · rcases certificate.chosen with ⟨empty, same⟩ | member
    · cases tails with
      | nil => exact .inl ⟨rfl, same⟩
      | cons first rest =>
        have firstEmpty : first = [] := by
          have absent := List.filter_eq_nil_iff.mp empty first (by simp)
          simpa using absent
        exact .inr (by simp [same, firstEmpty])
    · exact .inr (List.mem_filter.mp member).1
  · intro tail member
    by_cases empty : tail = []
    · subst tail; exact List.nil_suffix
    · exact certificate.containsTail tail (List.mem_filter.mpr ⟨member, by simpa using empty⟩)

private theorem cast_suffix_output (same : left = right) (certificate : SuffixCertified orders left) :
    (same ▸ certificate : SuffixCertified orders right).output = certificate.output := by
  cases same; rfl

theorem NodeCertified.restore_empty
    (certificate : NodeCertified name orders (tails.filter (fun tail => !tail.isEmpty))) :
    ∃ original : NodeCertified name orders tails,
      original.output = certificate.output ∧ original.selection.output = certificate.selection.output := by
  obtain ⟨selection, same⟩ := certificate.selection.restore_empty
  let ancestry : SuffixCertified orders selection.output := same.symm ▸ certificate.ancestry
  have output : ancestry.output = certificate.ancestry.output := cast_suffix_output same.symm _
  have unique : selection.output.Nodup := by rw [same]; exact certificate.tailUnique
  have fresh : name ∉ ancestry.output := by rw [output]; exact certificate.fresh
  exact ⟨⟨selection, ancestry, unique, fresh⟩, by simp [NodeCertified.output, output], same⟩

/-- Reintroduce every original parent edge and empty local order. The complete
output and selected tail survive this reverse normalization. -/
theorem nodeCertificate_expand
    (certificate : NodeCertified name
      ((unique names).map order ++ MergeState.pending locals) ((unique names).map parentTail)) :
    ∃ original : NodeCertified name (names.map order ++ locals) (names.map parentTail),
      original.output = certificate.output ∧ original.selection.output = certificate.selection.output := by
  let selection : TailCertified (names.map parentTail) := {
    output := certificate.selection.output
    chosen := by
      rcases certificate.selection.chosen with ⟨empty, same⟩ | member
      · have noNames : unique names = [] := List.map_eq_nil_iff.mp empty
        have originalEmpty : names = [] := by
          cases names with
          | nil => rfl
          | cons first rest =>
            have member : first ∈ unique (first :: rest) := unique_mem.mpr (by simp)
            rw [noNames] at member; cases member
        exact .inl ⟨by simp [originalEmpty], same⟩
      · obtain ⟨parent, present, same⟩ := List.mem_map.mp member
        exact .inr (List.mem_map.mpr ⟨parent, unique_mem.mp present, same⟩)
    containsTail := by
      intro tail member
      obtain ⟨parent, present, same⟩ := List.mem_map.mp member
      exact certificate.selection.containsTail tail
        (List.mem_map.mpr ⟨parent, unique_mem.mpr present, same⟩) }
  have normalized : Precedence.Trace
      (Precedence.candidates ((unique names).map order) (MergeState.pending locals) certificate.selection.output)
      certificate.ancestry.front := by
    simpa [Precedence.candidates, withoutTail, List.map_append] using certificate.ancestry.trace
  have expanded := (MergeState.trace_normalized_candidates names order locals certificate.selection.output).mpr normalized
  let ancestry : SuffixCertified (names.map order ++ locals) selection.output := {
    front := certificate.ancestry.front
    trace := by simpa [selection, Precedence.candidates, withoutTail, List.map_append] using expanded
    compatible := by
      intro input member
      rcases List.mem_append.mp member with parent | localOrder
      · obtain ⟨parent, present, same⟩ := List.mem_map.mp parent
        exact certificate.ancestry.compatible input
          (List.mem_append_left _ (List.mem_map.mpr ⟨parent, unique_mem.mpr present, same⟩))
      · by_cases empty : input = []
        · subst input; exact ⟨[], [], rfl, by simp, List.nil_sublist _⟩
        · exact certificate.ancestry.compatible input
            (List.mem_append_right _ (List.mem_filter.mpr ⟨localOrder, by simpa using empty⟩)) }
  exact ⟨⟨selection, ancestry, certificate.tailUnique, certificate.fresh⟩, rfl, rfl⟩

end LeanPoo.C4
