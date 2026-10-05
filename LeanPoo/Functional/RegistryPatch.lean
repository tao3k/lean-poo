import LeanPoo.Functional.SharedRegistry

/-! Typed capability edits with conservative root/checklist noninterference.
An unchanged graph order and provider/result families are retained. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- Replace or remove exactly one typed capability in a provider. -/
def Provider.patchKey (provider : Provider Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) : Provider Context Key Value :=
  fun query => if same : query = key then same.symm ▸ replacement else provider query

theorem Provider.patchKey_at (provider : Provider Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) :
    patchKey provider key replacement key = replacement := by simp [patchKey]

theorem Provider.patchKey_other (provider : Provider Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) (different : query ≠ key) :
    patchKey provider key replacement query = provider query := by simp [patchKey, different]

/-- Patch one existing provider; unknown names return their exact name as error.
No factory executes and no graph/order is reconstructed. The old table remains
usable. Hash storage may copy under sharing; no constant-time bound is claimed. -/
def ProviderRegistry.patch (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key))) :
    Except String (ProviderRegistry Context Key Value) :=
  match registry.entries[name]? with
  | none => .error name
  | some provider => .ok ⟨registry.entries.insert name (provider.patchKey key replacement)⟩

theorem ProviderRegistry.patch_missing (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key)))
    (missing : registry.entries[name]? = none) : patch registry name key replacement = .error name := by
  simp [patch, missing]

private theorem patch_success (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key)))
    (applied : registry.patch name key replacement = .ok updated) :
    ∃ provider, registry.entries[name]? = some provider ∧
      updated.entries = registry.entries.insert name (provider.patchKey key replacement) := by
  cases found : registry.entries[name]? with
  | none => simp [ProviderRegistry.patch, found] at applied
  | some provider =>
    refine ⟨provider, rfl, ?_⟩
    have same : (⟨registry.entries.insert name (provider.patchKey key replacement)⟩ :
        ProviderRegistry Context Key Value) = updated :=
      by simpa [ProviderRegistry.patch, found] using applied
    exact (congrArg ProviderRegistry.entries same).symm

/-- A successful edit changes exactly the selected cell. -/
theorem ProviderRegistry.patch_at (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key)))
    (applied : registry.patch name key replacement = .ok updated) :
    updated.dictionary name key = replacement := by
  obtain ⟨provider, _, table⟩ := patch_success registry name key replacement applied
  simp [dictionary, table, Provider.patchKey_at]

/-- Other provider names and other capability keys retain their exact functions. -/
theorem ProviderRegistry.patch_other (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key)))
    (applied : registry.patch name key replacement = .ok updated)
    (different : target ≠ name ∨ query ≠ key) :
    updated.dictionary target query = registry.dictionary target query := by
  obtain ⟨provider, found, table⟩ := patch_success registry name key replacement applied
  by_cases same : target = name
  · subst target
    have distinct : query ≠ key := different.resolve_left (by simp)
    simp [dictionary, table, found, Provider.patchKey_other _ _ _ distinct]
  · simp [dictionary, table, Std.HashMap.getElem?_insert, Ne.symm same]

/-- A patch never registers or removes a provider name; `none` removes only a
capability, not its provider entry. -/
theorem ProviderRegistry.patch_scope (registry : ProviderRegistry Context Key Value) (name : String)
    (key : Key) (replacement : Option (Factory Context (fun c => Value c key)))
    (applied : registry.patch name key replacement = .ok updated) :
    updated.entries.contains target = registry.entries.contains target := by
  obtain ⟨provider, found, table⟩ := patch_success registry name key replacement applied
  by_cases same : name = target
  · subst target
    simp [table, Std.HashMap.contains_eq_isSome_getElem?, found]
  · simp [table, Std.HashMap.contains_insert, same]

/-- Editing a cell outside a root/key read scope preserves the selected factory. -/
theorem assemble_patch_stable (order : C4.VerifiedOrder graph root)
    (registry : ProviderRegistry Context Key Value) (name : String) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key)))
    (applied : registry.patch name key replacement = .ok updated)
    (unaffected : ¬ C4.Ancestor graph name root ∨ query ≠ key) :
    assemble order updated.dictionary query = assemble order registry.dictionary query := by
  unfold assemble
  simpa using select_rename (providers := registry.dictionary) (names := order.output) (key := query)
    id updated.dictionary (fun target member => ProviderRegistry.patch_other registry name key replacement applied
      (unaffected.elim
        (fun outside => Or.inl (fun same => outside (same ▸ order.covers.mp member))) Or.inr))

theorem Requirements.prepare_patch_stable (order : C4.VerifiedOrder graph root)
    (registry : ProviderRegistry Context Key Value) (name : String) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) (keys : List Key)
    (applied : registry.patch name key replacement = .ok updated)
    (unaffected : ¬ C4.Ancestor graph name root ∨ key ∉ keys) :
    prepare (assemble order updated.dictionary) keys = prepare (assemble order registry.dictionary) keys := by
  apply prepare_congr
  intro query requested
  apply assemble_patch_stable order registry name key replacement applied
  exact unaffected.elim Or.inl (fun absent => Or.inr (fun same => absent (same ▸ requested)))

/-- Conservative candidate impact: ancestry plus an explicitly requested key.
True need not change selection (a more specific provider can shadow the edit). -/
def Requirements.mayAffect (index : C4.AncestryIndex graph root) (keys : List Key)
    (name : String) (key : Key) : Bool := index.isAncestor name && decide (key ∈ keys)

theorem Requirements.mayAffect_iff (index : C4.AncestryIndex graph root) (keys : List Key)
    (name : String) (key : Key) :
    mayAffect index keys name key = true ↔ C4.Ancestor graph name root ∧ key ∈ keys := by
  simp [mayAffect, index.isAncestor_iff]

/-- A negative impact query supplies exact checklist/function/error preservation. -/
theorem Requirements.prepare_patch_of_unaffected (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (name : String) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) (keys : List Key)
    (applied : registry.patch name key replacement = .ok updated)
    (unaffected : mayAffect index keys name key = false) :
    prepare (assemble index.order updated.dictionary) keys =
      prepare (assemble index.order registry.dictionary) keys := by
  apply prepare_patch_stable index.order registry name key replacement keys applied
  by_cases ancestor : C4.Ancestor graph name root
  · right
    intro requested
    have affected := (mayAffect_iff index keys name key).mpr ⟨ancestor, requested⟩
    simp [unaffected] at affected
  · exact Or.inl ancestor

end LeanPoo.Functional
