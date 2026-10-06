import LeanPoo.Functional.Overlay

/-! Install normalized typed capability batches at an existing provider name,
without rebuilding graph declarations or accumulating per-edit provider closures. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- One name lookup and one successful insertion for the entire batch. Unknown
names fail even for an empty batch. No factory executes and old snapshots remain
usable; normalized list construction and persistent hash copies still cost work. -/
def ProviderRegistry.patchBatch (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) : Except String (ProviderRegistry Context Key Value) :=
  match registry.entries[name]? with
  | none => .error name
  | some provider => .ok ⟨registry.entries.insert name (ProviderOverlay.compile provider edits).provider⟩

theorem ProviderRegistry.patchBatch_missing (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (absent : registry.entries[name]? = none) :
    patchBatch registry name edits = .error name := by simp [patchBatch, absent]

private theorem batch_success (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) :
    ∃ provider, registry.entries[name]? = some provider ∧
      updated.entries = registry.entries.insert name (ProviderOverlay.compile provider edits).provider := by
  cases found : registry.entries[name]? with
  | none => simp [ProviderRegistry.patchBatch, found] at applied
  | some provider =>
    refine ⟨provider, rfl, ?_⟩
    have same : (⟨registry.entries.insert name (ProviderOverlay.compile provider edits).provider⟩ :
        ProviderRegistry Context Key Value) = updated := by
      simpa [ProviderRegistry.patchBatch, found] using applied
    exact (congrArg ProviderRegistry.entries same).symm

/-- Exact single-provider batch semantics, including removals and repeated keys. -/
theorem ProviderRegistry.patchBatch_at (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) :
    updated.dictionary name =
      edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) (registry.dictionary name) := by
  obtain ⟨provider, found, table⟩ := batch_success registry name edits applied
  simp [dictionary, table, found, ProviderOverlay.compile_provider]

theorem ProviderRegistry.patchBatch_other (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) (different : target ≠ name) :
    updated.dictionary target = registry.dictionary target := by
  obtain ⟨provider, _, table⟩ := batch_success registry name edits applied
  simp [dictionary, table, Std.HashMap.getElem?_insert, Ne.symm different]

/-- Whole dictionary agreement with a sequential provider edit at one name.
This supplies a single rewrite for arbitrary dictionary/C4 clients. -/
theorem ProviderRegistry.patchBatch_dictionary (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) :
    updated.dictionary = fun target => if target = name then
      edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) (registry.dictionary name)
      else registry.dictionary target := by
  funext target
  by_cases same : target = name
  · subst target; simpa using patchBatch_at registry name edits applied
  · simpa [same] using patchBatch_other registry name edits applied same

/-- An empty batch at a known name preserves all dictionary functions. Unknown
names are still rejected; hash storage identity is not asserted. -/
theorem ProviderRegistry.patchBatch_nil (registry : ProviderRegistry Context Key Value) (name : String)
    (applied : registry.patchBatch name [] = .ok updated) : updated.dictionary = registry.dictionary := by
  rw [patchBatch_dictionary registry name [] applied]
  funext target
  by_cases same : target = name
  · subst target; simp
  · simp [same]

theorem ProviderRegistry.patchBatch_scope (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) :
    updated.entries.contains target = registry.entries.contains target := by
  obtain ⟨provider, found, table⟩ := batch_success registry name edits applied
  by_cases same : name = target
  · subst target; simp [table, Std.HashMap.contains_eq_isSome_getElem?, found]
  · simp [table, Std.HashMap.contains_insert, same]

private theorem fold_patch_untouched (edits : List (CapabilityEdit Context Key Value))
    (provider : Provider Context Key Value) (absent : query ∉ edits.map Sigma.fst) :
    (edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) provider) query = provider query := by
  induction edits generalizing provider with
  | nil => rfl
  | cons edit rest ih =>
    have scope : query ≠ edit.1 ∧ query ∉ rest.map Sigma.fst := by
      simpa only [List.map_cons, List.mem_cons, not_or] using absent
    rw [List.foldl_cons, ih _ scope.2, Provider.patchKey_other _ _ _ scope.1]

/-- A whole batch leaves unedited typed keys intact, even at its target name. -/
theorem ProviderRegistry.patchBatch_untouched (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value))
    (applied : registry.patchBatch name edits = .ok updated) (absent : query ∉ edits.map Sigma.fst) :
    updated.dictionary target query = registry.dictionary target query := by
  by_cases same : target = name
  · subst target
    rw [patchBatch_at registry name edits applied]
    exact fold_patch_untouched edits _ absent
  · rw [patchBatch_other registry name edits applied same]

/-- Negative ancestry or disjoint requested/edited keys preserve whole consumer
preparations across all contexts, with no per-provider alignment premises. -/
theorem Requirements.prepare_patchBatch_stable (order : C4.VerifiedOrder graph root)
    (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchBatch name edits = .ok updated)
    (unaffected : ¬ C4.Ancestor graph name root ∨ ∀ key ∈ keys, key ∉ edits.map Sigma.fst) :
    prepare (assemble order updated.dictionary) keys = prepare (assemble order registry.dictionary) keys := by
  apply prepare_congr
  intro query requested
  unfold assemble
  simpa using select_rename (providers := registry.dictionary) (names := order.output) (key := query)
    id updated.dictionary (fun target member => unaffected.elim
      (fun outside => congrFun (ProviderRegistry.patchBatch_other registry name edits applied
        (fun same => outside (same ▸ order.covers.mp member))) query)
      (fun disjoint => ProviderRegistry.patchBatch_untouched registry name edits applied (disjoint query requested)))

/-- Conservative batch impact: ancestry and overlap with caller-declared keys.
True may be shadowed or blocked by an earlier missing key. -/
def Requirements.batchMayAffect (index : C4.AncestryIndex graph root) (keys : List Key)
    (name : String) (edits : List (CapabilityEdit Context Key Value)) : Bool :=
  index.isAncestor name && edits.any (fun edit => decide (edit.1 ∈ keys))

theorem Requirements.batchMayAffect_iff (index : C4.AncestryIndex graph root) (keys : List Key)
    (name : String) (edits : List (CapabilityEdit Context Key Value)) :
    batchMayAffect index keys name edits = true ↔
      C4.Ancestor graph name root ∧ ∃ edit ∈ edits, edit.1 ∈ keys := by
  simp [batchMayAffect, index.isAncestor_iff]

theorem Requirements.prepare_patchBatch_of_unaffected (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchBatch name edits = .ok updated)
    (unaffected : batchMayAffect index keys name edits = false) :
    prepare (assemble index.order updated.dictionary) keys = prepare (assemble index.order registry.dictionary) keys := by
  apply prepare_patchBatch_stable index.order registry name edits keys applied
  by_cases ancestor : C4.Ancestor graph name root
  · right
    intro key requested edited
    obtain ⟨edit, member, same⟩ := List.mem_map.mp edited
    have affected := (batchMayAffect_iff index keys name edits).mpr ⟨ancestor, edit, member, same ▸ requested⟩
    simp [unaffected] at affected
  · exact Or.inl ancestor

end LeanPoo.Functional
