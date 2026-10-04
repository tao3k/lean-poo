import LeanPoo.C4.TraversalInvariant

namespace LeanPoo.C4.LinearizeState

/-- A chosen suffix reaches every supplied nonempty suffix through actual
inherited-suffix pointers. Empty metadata contributes no obligation. -/
def SuffixDominates (table : Table) (chosen source : Option String) : Prop :=
  match source with
  | none => True
  | some target => ∃ name, chosen = some name ∧ ∃ steps, SuffixPath table name target steps

theorem SuffixDominates.refl (table : Table) (source : Option String) :
    SuffixDominates table source source := by
  cases source with
  | none => trivial
  | some name => exact ⟨name, rfl, 0, .here⟩

theorem SuffixDominates.trans (first : SuffixDominates table last middle)
    (second : SuffixDominates table middle source) : SuffixDominates table last source := by
  cases source with
  | none => trivial
  | some target =>
    obtain ⟨name, same, steps, path⟩ := second
    subst middle
    obtain ⟨final, same, count, before⟩ := first
    exact ⟨final, same, steps + count, before.trans path⟩

/-- A successful runtime comparison retains an input and dominates both. -/
theorem selectSuffixStep_sound
    (success : selectSuffixStep table current next = .ok chosen) :
    (chosen = current ∨ chosen = next) ∧
      SuffixDominates table chosen current ∧ SuffixDominates table chosen next := by
  cases current with
  | none =>
    simp only [selectSuffixStep, Except.ok.injEq] at success
    subst chosen
    exact ⟨.inr rfl, trivial, .refl table next⟩
  | some current =>
    cases next with
    | none =>
      simp only [selectSuffixStep, Except.ok.injEq] at success
      subst chosen
      exact ⟨.inl rfl, .refl table _, trivial⟩
    | some next =>
      by_cases forward : suffixReaches table current next = true
      · simp [selectSuffixStep, forward] at success
        subst chosen
        obtain ⟨steps, path⟩ := suffixReaches_sound forward
        exact ⟨.inl rfl, .refl table _, ⟨current, rfl, steps, path⟩⟩
      · by_cases backward : suffixReaches table next current = true
        · simp [selectSuffixStep, forward, backward] at success
          subst chosen
          obtain ⟨steps, path⟩ := suffixReaches_sound backward
          exact ⟨.inr rfl, ⟨next, rfl, steps, path⟩, .refl table _⟩
        · simp [selectSuffixStep, forward, backward] at success

/-- All successful parent folds retain one input and dominate every input,
including their initial accumulator. No cache validity is assumed here. -/
theorem selectSuffix_sound
    (success : selectSuffix table sources initial = .ok chosen) :
    (chosen = initial ∨ chosen ∈ sources) ∧
      ∀ source ∈ initial :: sources, SuffixDominates table chosen source := by
  induction sources generalizing initial with
  | nil =>
    simp only [selectSuffix, Except.ok.injEq] at success
    subst chosen
    exact ⟨.inl rfl, by
      intro source member
      have same : source = initial := by simpa using member
      subst source
      exact .refl table initial⟩
  | cons next rest ih =>
    cases step : selectSuffixStep table initial next with
    | error error => simp [selectSuffix, step, bind, Except.bind] at success
    | ok middle =>
      have remaining : selectSuffix table rest middle = .ok chosen := by
        simpa [selectSuffix, step, bind, Except.bind] using success
      obtain ⟨retained, dominates⟩ := ih remaining
      obtain ⟨input, first, second⟩ := selectSuffixStep_sound step
      refine ⟨?_, ?_⟩
      · rcases retained with same | member
        · rcases input with before | after
          · exact .inl (same.trans before)
          · exact .inr (List.mem_cons.mpr (.inl (same.trans after)))
        · exact .inr (List.mem_cons_of_mem next member)
      · intro source member
        rcases List.mem_cons.mp member with same | member
        · subst source
          exact (dominates middle List.mem_cons_self).trans first
        · rcases List.mem_cons.mp member with same | member
          · subst source
            exact (dominates middle List.mem_cons_self).trans second
          · exact dominates source (List.mem_cons_of_mem middle member)

/-- Comparable pointer chains cannot be rejected by the bounded comparison. -/
theorem selectSuffixStep_complete (valid : SuffixCacheInvariant table)
    (comparable : SuffixDominates table current next ∨ SuffixDominates table next current) :
    ∃ chosen, selectSuffixStep table current next = .ok chosen := by
  cases current with
  | none => exact ⟨next, rfl⟩
  | some current =>
    cases next with
    | none => exact ⟨some current, rfl⟩
    | some next =>
      rcases comparable with forward | backward
      · obtain ⟨name, same, steps, path⟩ := forward
        have names : current = name := Option.some.inj same
        subst name
        exact ⟨some current, by simp [selectSuffixStep, suffixReaches_complete valid path]⟩
      · obtain ⟨name, same, steps, path⟩ := backward
        have names : next = name := Option.some.inj same
        subst name
        by_cases forward : suffixReaches table current next = true
        · exact ⟨some current, by simp [selectSuffixStep, forward]⟩
        · exact ⟨some next, by simp [selectSuffixStep, forward,
            suffixReaches_complete valid path]⟩

/-- Pairwise comparable supplied pointer chains suffice for successful
selection with the runtime's unchanged table-size walk budget. -/
theorem selectSuffix_complete (valid : SuffixCacheInvariant table)
    (comparable : ∀ left ∈ initial :: sources, ∀ right ∈ initial :: sources,
      SuffixDominates table left right ∨ SuffixDominates table right left) :
    ∃ chosen, selectSuffix table sources initial = .ok chosen := by
  induction sources generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons next rest ih =>
    obtain ⟨middle, step⟩ := selectSuffixStep_complete valid
      (comparable initial List.mem_cons_self next
        (List.mem_cons_of_mem initial List.mem_cons_self))
    have retained := (selectSuffixStep_sound step).1
    have subset : ∀ source ∈ middle :: rest, source ∈ initial :: next :: rest := by
      intro source member
      rcases List.mem_cons.mp member with same | member
      · subst source
        rcases retained with same | same
        · rw [same]; exact List.mem_cons_self
        · rw [same]; exact List.mem_cons_of_mem initial List.mem_cons_self
      · exact List.mem_cons_of_mem initial (List.mem_cons_of_mem next member)
    obtain ⟨chosen, success⟩ := ih (fun left first right second =>
      comparable left (subset left first) right (subset right second))
    exact ⟨chosen, by simp [selectSuffix, step, success, bind, Except.bind]⟩

/-- Under the cache-link invariant, selected metadata preserves each supplied
suffix as a literal suffix of the selected cached precedence. -/
theorem selectSuffix_preserves (valid : SuffixCacheInvariant table)
    (success : selectSuffix table sources none = .ok (some chosen))
    (found : lookup table chosen = some entry) (member : some source ∈ sources) :
    ∃ child, lookup table source = some child ∧ child.precedence.IsSuffix entry.precedence := by
  obtain ⟨name, same, steps, path⟩ :=
    (selectSuffix_sound success).2 (some source) (List.mem_cons_of_mem none member)
  have names : chosen = name := Option.some.inj same
  subst name
  obtain ⟨child, cached, suffix, _⟩ := path.endpoint valid found
  exact ⟨child, cached, suffix⟩

/-- Cached full precedences contributed by nonempty parent suffix metadata. -/
def suffixTails (table : Table) (sources : List (Option String)) : List (List String) :=
  sources.filterMap (fun source => (source.bind (lookup table)).map (·.precedence))

def selectedTail (table : Table) (chosen : Option String) : List String :=
  ((chosen.bind (lookup table)).map (·.precedence)).getD []

/-- Successful selection supplies the independent tail certificate when its
chosen cache entry exists. This does not infer canonical parent metadata. -/
theorem selectSuffix_tailCertified (valid : SuffixCacheInvariant table)
    (success : selectSuffix table sources none = .ok chosen)
    (available : ∀ name, chosen = some name → ∃ entry, lookup table name = some entry) :
    ∃ certificate : TailCertified (suffixTails table sources),
      certificate.output = selectedTail table chosen := by
  refine ⟨⟨selectedTail table chosen, ?_, ?_⟩, rfl⟩
  · cases chosen with
    | none =>
      refine .inl ⟨?_, rfl⟩
      apply List.filterMap_eq_nil_iff.mpr
      intro source member
      have dominates := (selectSuffix_sound success).2 source
        (List.mem_cons_of_mem none member)
      cases source with
      | none => rfl
      | some name =>
        obtain ⟨name, impossible, _⟩ := dominates
        cases impossible
    | some name =>
      obtain ⟨entry, found⟩ := available name rfl
      have member : some name ∈ sources := by
        rcases (selectSuffix_sound success).1 with impossible | member
        · cases impossible
        · exact member
      apply Or.inr
      apply List.mem_filterMap.mpr
      exact ⟨some name, member, by simp [selectedTail, found]⟩
  · intro tail member
    obtain ⟨source, present, cached⟩ := List.mem_filterMap.mp member
    cases source with
    | none => simp at cached
    | some source =>
      cases chosen with
      | none =>
        obtain ⟨name, impossible, _⟩ := (selectSuffix_sound success).2 (some source)
          (List.mem_cons_of_mem none present)
        cases impossible
      | some name =>
        obtain ⟨entry, found⟩ := available name rfl
        obtain ⟨child, lookup, suffix⟩ := selectSuffix_preserves valid success found present
        have same : child.precedence = tail := by simpa [lookup] using cached
        simpa [selectedTail, found, same] using suffix

end LeanPoo.C4.LinearizeState
