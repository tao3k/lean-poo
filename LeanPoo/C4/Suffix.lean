import LeanPoo.C4.MergeInvariant

namespace LeanPoo.C4

def withoutTail (items tail : List String) : List String :=
  items.filter (fun item => !tail.contains item)

/-- Suffix members form the final part of an input order, in inherited-tail order. -/
def respectsSuffixTail (order tail : List String) : Bool :=
  let suffix := order.dropWhile (fun item => !tail.contains item)
  suffix.all tail.contains &&
    tail.filter (fun item => suffix.contains item) == suffix

/-- The split required by C4 cleanup: an infix prefix followed by an ordered
sublist of the shared suffix. -/
def SuffixCompatible (order tail : List String) : Prop :=
  ∃ front suffix, order = front ++ suffix ∧
    (∀ name ∈ front, name ∉ tail) ∧ suffix.Sublist tail

theorem respectsSuffixTail_sound (accepted : respectsSuffixTail order tail = true) :
    SuffixCompatible order tail := by
  let front := order.takeWhile (fun item => !tail.contains item)
  let suffix := order.dropWhile (fun item => !tail.contains item)
  have parts : front ++ suffix = order := List.takeWhile_append_dropWhile
  have suffixEq : tail.filter (fun item => suffix.contains item) = suffix := by
    have both : suffix.all tail.contains = true ∧
        (tail.filter (fun item => suffix.contains item) == suffix) = true := by
      simpa [respectsSuffixTail, suffix] using accepted
    exact beq_iff_eq.mp both.2
  refine ⟨front, suffix, parts.symm, ?_, ?_⟩
  · intro name member
    have allowed := List.all_eq_true.mp List.all_takeWhile name member
    simpa using allowed
  · rw [← suffixEq]
    exact List.filter_sublist

theorem compatible_withoutTail (compatible : SuffixCompatible order tail) :
    ∃ suffix, order = withoutTail order tail ++ suffix ∧ suffix.Sublist tail := by
  obtain ⟨front, suffix, same, absent, contained⟩ := compatible
  have frontKept : withoutTail front tail = front :=
    List.filter_eq_self.mpr (by simpa using absent)
  have suffixRemoved : withoutTail suffix tail = [] :=
    List.filter_eq_nil_iff.mpr (by
      intro name member
      have present := contained.subset member
      simpa using present)
  have cleaned : withoutTail order tail = front := by
    rw [same]
    change (front ++ suffix).filter _ = front
    rw [List.filter_append]
    change withoutTail front tail ++ withoutTail suffix tail = front
    rw [frontKept, suffixRemoved, List.append_nil]
  exact ⟨suffix, by rw [cleaned]; exact same, contained⟩

/-- Every compatible order passes the executable check when the shared tail
has no repeated names. -/
theorem respectsSuffixTail_complete (compatible : SuffixCompatible order tail)
    (unique : tail.Nodup) : respectsSuffixTail order tail = true := by
  obtain ⟨front, suffix, same, absent, contained⟩ := compatible
  have dropped : order.dropWhile (fun item => !tail.contains item) = suffix := by
    rw [same, List.dropWhile_append_of_pos (by simpa using absent)]
    cases suffix with
    | nil => rfl
    | cons name rest =>
      have member := contained.subset (List.mem_cons_self)
      simp [member]
  have filtered : tail.filter (fun item => suffix.contains item) = suffix := by
    have kept : suffix.Sublist (tail.filter (fun item => suffix.contains item)) :=
      List.sublist_filter_iff.mpr ⟨suffix, contained, (List.filter_eq_self.mpr (by simp)).symm⟩
    exact (kept.eq_of_length_le ((unique.sublist List.filter_sublist).length_le_of_subset
      (by intro name member; simpa using (List.mem_filter.mp member).2))).symm
  simp only [respectsSuffixTail, dropped, filtered, beq_self_eq_true, Bool.and_true]
  exact List.all_eq_true.mpr (by intro name member; simpa using contained.subset member)

theorem respectsSuffixTail_iff (unique : tail.Nodup) :
    respectsSuffixTail order tail = true ↔ SuffixCompatible order tail :=
  ⟨respectsSuffixTail_sound, fun compatible => respectsSuffixTail_complete compatible unique⟩

/-- Reattaching a compatible shared tail preserves the complete input order. -/
theorem append_preserves (trace : Precedence.Trace lists front)
    (member : withoutTail order tail ∈ lists)
    (compatible : SuffixCompatible order tail) : order.Sublist (front ++ tail) := by
  obtain ⟨suffix, same, contained⟩ := compatible_withoutTail compatible
  rw [same]
  exact (trace.preserves member).append contained

/-- Evidence for the complete merged ancestry, including the inherited tail. -/
structure SuffixCertified (orders : List (List String)) (tail : List String) where
  front : List String
  trace : Precedence.Trace (orders.map (fun order => withoutTail order tail)) front
  compatible : ∀ order ∈ orders, SuffixCompatible order tail

def SuffixCertified.output (certificate : SuffixCertified orders tail) : List String :=
  certificate.front ++ tail

theorem SuffixCertified.preserves (certificate : SuffixCertified orders tail)
    (member : order ∈ orders) : order.Sublist certificate.output :=
  append_preserves certificate.trace (List.mem_map.mpr ⟨order, member, rfl⟩)
    (certificate.compatible order member)

theorem SuffixCertified.suffix (certificate : SuffixCertified orders tail) :
    tail.IsSuffix certificate.output := ⟨certificate.front, rfl⟩

theorem SuffixCertified.front_excludes (certificate : SuffixCertified orders tail)
    (member : name ∈ certificate.front) : name ∉ tail := by
  obtain ⟨cleaned, present, contains⟩ := certificate.trace.covers.mp member
  obtain ⟨order, _, same⟩ := List.mem_map.mp present
  subst cleaned
  exact by simpa [withoutTail] using (List.mem_filter.mp contains).2

theorem SuffixCertified.covers (certificate : SuffixCertified orders tail) :
    name ∈ certificate.output ↔ (∃ order ∈ orders, name ∈ order) ∨ name ∈ tail := by
  constructor
  · intro member
    rcases List.mem_append.mp member with frontMember | tailMember
    · obtain ⟨cleaned, present, contains⟩ := certificate.trace.covers.mp frontMember
      obtain ⟨order, originalPresent, same⟩ := List.mem_map.mp present
      subst cleaned
      exact .inl ⟨order, originalPresent, (List.mem_filter.mp contains).1⟩
    · exact .inr tailMember
  · rintro (⟨order, present, contains⟩ | tailMember)
    · exact (certificate.preserves present).subset contains
    · exact certificate.suffix.sublist.subset tailMember

theorem SuffixCertified.nodup (certificate : SuffixCertified orders tail)
    (tailUnique : tail.Nodup) : certificate.output.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨certificate.trace.nodup, tailUnique, ?_⟩
  intro first member second present same
  subst second
  exact certificate.front_excludes member present

/-- Check complete parent and local orders before cleanup; then certify the
prefix merge and reattach the shared suffix with an order-preservation proof. -/
private def mergeWithSuffixUsing
    (merger : (lists : List (List String)) → Except Error (Precedence.Certified lists))
    (orders : List (List String)) (tail : List String) :
    Except Error (SuffixCertified orders tail) := do
  if accepted : orders.all (fun order => respectsSuffixTail order tail) = true then
    let merged ← merger (orders.map (fun order => withoutTail order tail))
    return ⟨merged.output, merged.trace, fun order member =>
      respectsSuffixTail_sound (List.all_eq_true.mp accepted order member)⟩
  else throw .suffixOrderViolation

def mergeWithSuffixCertified (orders : List (List String)) (tail : List String) :
    Except Error (SuffixCertified orders tail) :=
  mergeWithSuffixUsing Precedence.mergeCertified orders tail

/-- Suffix reconstruction with the complete structural reference merger. -/
def mergeWithSuffixReference (orders : List (List String)) (tail : List String) :
    Except Error (SuffixCertified orders tail) :=
  mergeWithSuffixUsing Precedence.mergeReference orders tail

theorem mergeWithSuffixReference_complete (certificate : SuffixCertified orders tail)
    (unique : tail.Nodup) :
    ∃ result, mergeWithSuffixReference orders tail = .ok result ∧
      result.output = certificate.output := by
  have accepted : orders.all (fun order => respectsSuffixTail order tail) = true :=
    List.all_eq_true.mpr (fun order member =>
      respectsSuffixTail_complete (certificate.compatible order member) unique)
  obtain ⟨merged, success, same⟩ := Precedence.mergeReference_complete certificate.trace
  refine ⟨⟨merged.output, merged.trace, fun order member =>
    respectsSuffixTail_sound (List.all_eq_true.mp accepted order member)⟩, ?_, ?_⟩
  · simp [mergeWithSuffixReference, mergeWithSuffixUsing, accepted, success]
    rfl
  · simp [SuffixCertified.output, same]

/-- The optimized merger also reconstructs every compatible suffix certificate. -/
theorem mergeWithSuffixCertified_complete (certificate : SuffixCertified orders tail)
    (unique : tail.Nodup) :
    ∃ result, mergeWithSuffixCertified orders tail = .ok result ∧
      result.output = certificate.output := by
  have accepted : orders.all (fun order => respectsSuffixTail order tail) = true :=
    List.all_eq_true.mpr (fun order member =>
      respectsSuffixTail_complete (certificate.compatible order member) unique)
  obtain ⟨merged, success, same⟩ := Precedence.mergeCertified_complete certificate.trace
  refine ⟨⟨merged.output, merged.trace, fun order member =>
    respectsSuffixTail_sound (List.all_eq_true.mp accepted order member)⟩, ?_, ?_⟩
  · simp [mergeWithSuffixCertified, mergeWithSuffixUsing, accepted, success]
    rfl
  · simp [SuffixCertified.output, same]

end LeanPoo.C4
