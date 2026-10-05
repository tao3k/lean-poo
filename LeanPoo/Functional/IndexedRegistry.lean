import LeanPoo.Functional.IndexedOverlay
import LeanPoo.Functional.RegistryBatch

/-! Retain per-name indexed overlays across updates. Dictionary queries do not
materialize another registry or rebuild the declaration table. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

structure IndexedRegistry (Context : Type u) (Key : Type v) (Value : Context → Key → Type w)
    [BEq Key] [Hashable Key] where
  entries : Std.HashMap String (IndexedOverlay Context Key Value)

/-- Convert once from an existing scoped registry; no factory executes. -/
def IndexedRegistry.ofRegistry (registry : ProviderRegistry Context Key Value) : IndexedRegistry Context Key Value :=
  ⟨registry.entries.map (fun _ provider => IndexedOverlay.ofProvider provider)⟩

def IndexedRegistry.dictionary (registry : IndexedRegistry Context Key Value)
    (name : String) : Provider Context Key Value :=
  match registry.entries[name]? with
  | none => fun _ => none
  | some state => state.provider

/-- Optional materialization for APIs requiring a concrete ProviderRegistry.
This maps the full table; prefer dictionary directly in repeated query loops. -/
def IndexedRegistry.snapshot (registry : IndexedRegistry Context Key Value) : ProviderRegistry Context Key Value :=
  ⟨registry.entries.map (fun _ state => state.provider)⟩

omit [DecidableEq Key] in
theorem IndexedRegistry.snapshot_dictionary (registry : IndexedRegistry Context Key Value) :
    registry.snapshot.dictionary = registry.dictionary := by
  funext name
  simp only [snapshot, ProviderRegistry.dictionary, dictionary, Std.HashMap.getElem?_map]
  cases registry.entries[name]? <;> rfl

omit [DecidableEq Key] in
theorem IndexedRegistry.ofRegistry_dictionary (registry : ProviderRegistry Context Key Value) :
    (ofRegistry registry).dictionary = registry.dictionary := by
  funext name
  simp only [ofRegistry, dictionary, Std.HashMap.getElem?_map]
  cases found : registry.entries[name]? <;> simp [ProviderRegistry.dictionary, found, IndexedOverlay.ofProvider_provider]

/-- One name lookup/insertion per successful batch, extending retained typed
state instead of wrapping its previous provider. Unknown names still fail. -/
def IndexedRegistry.patchBatch (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) : Except String (IndexedRegistry Context Key Value) :=
  match registry.entries[name]? with
  | none => .error name
  | some state => .ok ⟨registry.entries.insert name (state.extend edits)⟩

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.patchBatch_missing (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (absent : registry.entries[name]? = none) :
    registry.patchBatch name edits = .error name := by simp [patchBatch, absent]

omit [LawfulBEq Key] [DecidableEq Key] in
private theorem indexed_success (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated) :
    ∃ state, registry.entries[name]? = some state ∧ updated.entries = registry.entries.insert name (state.extend edits) := by
  cases found : registry.entries[name]? with
  | none => simp [IndexedRegistry.patchBatch, found] at applied
  | some state =>
    refine ⟨state, rfl, ?_⟩
    have same : (⟨registry.entries.insert name (state.extend edits)⟩ : IndexedRegistry Context Key Value) = updated := by
      simpa [IndexedRegistry.patchBatch, found] using applied
    exact (congrArg IndexedRegistry.entries same).symm

theorem IndexedRegistry.patchBatch_at (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated) :
    updated.dictionary name = edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) (registry.dictionary name) := by
  obtain ⟨state, found, table⟩ := indexed_success registry name edits applied
  simp [dictionary, table, found, IndexedOverlay.extend_provider]

omit [DecidableEq Key] in
theorem IndexedRegistry.patchBatch_other (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated)
    (different : target ≠ name) : updated.dictionary target = registry.dictionary target := by
  obtain ⟨state, _, table⟩ := indexed_success registry name edits applied
  simp [dictionary, table, Std.HashMap.getElem?_insert, Ne.symm different]

omit [LawfulBEq Key] [DecidableEq Key] in
/-- Original bases remain fixed at every name, across arbitrarily many batches. -/
theorem IndexedRegistry.patchBatch_base (registry : IndexedRegistry Context Key Value) (name target : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated) :
    (updated.entries[target]?).map (fun state : IndexedOverlay Context Key Value => state.base) = (registry.entries[target]?).map (fun state : IndexedOverlay Context Key Value => state.base) := by
  obtain ⟨state, found, table⟩ := indexed_success registry name edits applied
  by_cases same : target = name
  · subst target; simp [table, found, IndexedOverlay.extend_base]
  · simp [table, Std.HashMap.getElem?_insert, Ne.symm same]

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.patchBatch_scope (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated) :
    updated.entries.contains target = registry.entries.contains target := by
  obtain ⟨state, found, table⟩ := indexed_success registry name edits applied
  by_cases same : name = target
  · subst target; simp [table, Std.HashMap.contains_eq_isSome_getElem?, found]
  · simp [table, Std.HashMap.contains_insert, same]

/-- Reuse the existing batch contract by exact whole-dictionary agreement.
Snapshots here occur in proof premises; dictionary clients need not materialize. -/
theorem IndexedRegistry.patchBatch_agreement (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (applied : registry.patchBatch name edits = .ok updated)
    (reference : registry.snapshot.patchBatch name edits = .ok ordinary) :
    updated.dictionary = ordinary.dictionary := by
  funext target
  by_cases same : target = name
  · subst target
    rw [patchBatch_at registry name edits applied, ProviderRegistry.patchBatch_at registry.snapshot name edits reference,
      snapshot_dictionary]
  · rw [patchBatch_other registry name edits applied same,
      ProviderRegistry.patchBatch_other registry.snapshot name edits reference same, snapshot_dictionary]

theorem Requirements.prepare_indexedRegistry_of_unaffected (index : C4.AncestryIndex graph root)
    (registry : IndexedRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchBatch name edits = .ok updated)
    (unaffected : batchMayAffect index keys name edits = false) :
    prepare (assemble index.order updated.dictionary) keys = prepare (assemble index.order registry.dictionary) keys := by
  obtain ⟨state, found, _⟩ := indexed_success registry name edits applied
  let ordinary : ProviderRegistry Context Key Value :=
    ⟨registry.snapshot.entries.insert name (ProviderOverlay.compile state.provider edits).provider⟩
  have reference : registry.snapshot.patchBatch name edits = .ok ordinary := by
    simp [ProviderRegistry.patchBatch, IndexedRegistry.snapshot, Std.HashMap.getElem?_map, found, ordinary]
  rw [IndexedRegistry.patchBatch_agreement registry name edits applied reference]
  simpa only [IndexedRegistry.snapshot_dictionary] using
    prepare_patchBatch_of_unaffected index registry.snapshot name edits keys reference unaffected

end LeanPoo.Functional
