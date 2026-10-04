import LeanPoo.C4.MetadataInvariant

namespace LeanPoo.Tests.MetadataInvariant
open C4 LinearizeState

example (trace : GraphTrace graph root output tail) :
    tail = [] ∨ ∃ name node, graph.findNode? name = some node ∧ node.suffix = true ∧
      Ancestor graph name root ∧ GraphTrace graph name tail tail := trace.tail_origin
example (valid : MetadataInvariant graph table) (found : lookup table source = some entry)
    (declared : graph.findNode? target = some node) (marked : node.suffix = true) :
    suffixReaches table source target = true ↔ Ancestor graph target source :=
  suffixReaches_flagged_iff valid found declared marked
example (valid : MetadataInvariant graph table) (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) :
    ∃ chosen, selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen :=
  collected_suffix_selection_complete valid trace found collected
example (valid : MetadataInvariant graph table) (collected : collectParents table names = .ok entries)
    (success : selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen) :
    ∃ certificate : TailCertified (suffixTails table (entries.map (·.mostSpecificSuffix))),
      certificate.output = selectedTail table chosen :=
  collected_suffix_selection_certified valid collected success

/- The earlier link invariant permits a skipped suffix ancestor. This
kernel-checked counterexample records why semantic coverage is necessary. -/
private def t : Linearization := ⟨["T"], none, some "T"⟩
private def s : Linearization := ⟨["S", "T"], none, some "S"⟩
private def skipped : Table := ({} : Table).insert "T" t |>.insert "S" s
private def graph : Graph :=
  { nodes := [{ name := "T", suffix := true },
      { name := "S", parentOrders := [["T"]], suffix := true }] }

private theorem skipped_entries (found : lookup skipped name = some entry) :
    (name = "S" ∧ entry = s) ∨ (name = "T" ∧ entry = t) := by
  by_cases first : "S" = name
  · subst name
    have same : s = entry := by simpa [skipped, lookup_insert] using found
    exact .inl ⟨rfl, same.symm⟩
  · by_cases second : "T" = name
    · subst name
      have same : t = entry := by simpa [skipped, lookup_insert] using found
      exact .inr ⟨rfl, same.symm⟩
    · simp [skipped, lookup, first, second] at found

private theorem skipped_weak_valid : SuffixCacheInvariant skipped := by
  constructor
  · intro name entry found
    rcases skipped_entries found with ⟨same, cached⟩ | ⟨same, cached⟩ <;>
      subst name <;> subst entry <;> rfl
  · intro name entry found next link
    rcases skipped_entries found with ⟨_, cached⟩ | ⟨_, cached⟩ <;>
      subst entry <;> cases link

private theorem skipped_ancestor : Ancestor graph "T" "S" :=
  .parent (node := { name := "S", parentOrders := [["T"]], suffix := true })
    rfl (by decide) .self
private theorem skipped_rejected : suffixReaches skipped "S" "T" = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨steps, path⟩ := suffixReaches_sound accepted
  generalize targetEq : "T" = target at path
  cases path with
  | here => exact (by decide : ("T" : String) ≠ "S") targetEq
  | next found link rest =>
    have cached : lookup skipped "S" = some s := by simp [skipped, lookup_insert]
    have same := Option.some.inj (found.symm.trans cached)
    subst_vars
    cases link
private theorem skipped_not_metadata : ¬ MetadataInvariant graph skipped := by
  intro valid
  have found : lookup skipped "S" = some s := by simp [skipped, lookup_insert]
  have accepted := (suffixReaches_flagged_iff valid found
    (node := { name := "T", suffix := true }) rfl rfl).mpr skipped_ancestor
  rw [skipped_rejected] at accepted
  cases accepted

example : SuffixCacheInvariant skipped := skipped_weak_valid
example : ¬ MetadataInvariant graph skipped := skipped_not_metadata
#guard !suffixReaches skipped "S" "T"
#guard (linearize graph "S").toOption == some ["S", "T"]
#guard (linearizeChecked graph "S").toOption == some ["S", "T"]
#guard (suffixTails skipped [none, some "T", some "S"]) == [["T"], ["S", "T"]]

#print axioms GraphTrace.tail_origin
#print axioms GraphTrace.tail_empty_iff
#print axioms MetadataInvariant.empty
#print axioms selected_suffix_declared
#print axioms metadata_none_iff
#print axioms metadata_selected_ancestor
#print axioms flagged_ancestor_path
#print axioms suffixReaches_flagged_iff
#print axioms metadata_tail_preserves
#print axioms literal_suffix_path
#print axioms parent_metadata_comparable
#print axioms collected_suffix_selection_complete
#print axioms collected_suffix_selection_certified
#print axioms skipped_weak_valid
#print axioms skipped_not_metadata
#eval IO.println "METADATA-INVARIANT-OK"

end LeanPoo.Tests.MetadataInvariant
