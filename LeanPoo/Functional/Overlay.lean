import LeanPoo.Functional.RegistryPatch

/-! A finite, typed capability overlay with one stored edit per key. Queries
scan current overrides, not the history of edits. Factory bodies never run. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- An explicit removal (`none`) is different from having no override. -/
abbrev CapabilityEdit (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) :=
  (key : Key) × Option (Factory Context (fun c => Value c key))

private def overlaySelect (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (query : Key) :
    Option (Factory Context (fun c => Value c query)) :=
  match edits with
  | [] => base query
  | ⟨key, replacement⟩ :: rest =>
    if same : query = key then same.symm ▸ replacement else overlaySelect base rest query

private theorem overlaySelect_filter (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (key query : Key) (different : query ≠ key) :
    overlaySelect base (edits.filter (fun edit => !decide (edit.1 = key))) query =
      overlaySelect base edits query := by
  induction edits with
  | nil => rfl
  | cons edit rest ih =>
    rcases edit with ⟨target, replacement⟩
    by_cases removed : target = key
    · subst target
      simp [overlaySelect, different, ih]
    · by_cases same : query = target
      · simp [overlaySelect, removed, same]
      · simp [overlaySelect, removed, same, ih]

/-- Retain an original provider and a normalized finite set of typed overrides.
The base can itself have costs; this structure does not compact its internals. -/
structure ProviderOverlay (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) where
  base : Provider Context Key Value
  edits : List (CapabilityEdit Context Key Value)
  unique : (edits.map Sigma.fst).Nodup

/-- Start once from the original provider, with no overrides. -/
def ProviderOverlay.ofProvider (base : Provider Context Key Value) : ProviderOverlay Context Key Value :=
  ⟨base, [], by simp⟩

/-- Materialize the provider interface without building per-edit closures. -/
def ProviderOverlay.provider (overlay : ProviderOverlay Context Key Value) : Provider Context Key Value :=
  overlaySelect overlay.base overlay.edits

/-- Keep only the latest edit of this key, including explicit removal. A set
scans the current overrides once; it never invokes factories or changes base. -/
def ProviderOverlay.set (overlay : ProviderOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) : ProviderOverlay Context Key Value :=
  ⟨overlay.base, ⟨key, replacement⟩ :: overlay.edits.filter (fun edit => !decide (edit.1 = key)), by
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · simp
    · simpa only [List.nodup_iff_pairwise_ne, List.filter_map, Function.comp_def] using overlay.unique.filter (fun query => !decide (query = key))⟩

/-- Normalized storage has exactly the existing single-key edit semantics. -/
theorem ProviderOverlay.set_provider (overlay : ProviderOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) :
    (overlay.set key replacement).provider = overlay.provider.patchKey key replacement := by
  funext query
  by_cases same : query = key
  · subst query; simp [set, provider, overlaySelect, Provider.patchKey]
  · simp [set, provider, overlaySelect, Provider.patchKey, same,
      overlaySelect_filter overlay.base overlay.edits key query same]

@[simp] theorem ProviderOverlay.ofProvider_provider (base : Provider Context Key Value) :
    (ofProvider base).provider = base := rfl

/-- Compile a batch in caller order. Normalization is per key: later edits win,
while untouched capabilities still delegate to the retained original provider. -/
def ProviderOverlay.compile (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) : ProviderOverlay Context Key Value :=
  edits.foldl (fun overlay edit => overlay.set edit.1 edit.2) (ofProvider base)

private theorem fold_set_provider (edits : List (CapabilityEdit Context Key Value))
    (overlay : ProviderOverlay Context Key Value) :
    (edits.foldl (fun state edit => state.set edit.1 edit.2) overlay).provider =
      edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) overlay.provider := by
  induction edits generalizing overlay with
  | nil => rfl
  | cons edit rest ih =>
    simp only [List.foldl_cons, ih, ProviderOverlay.set_provider]

/-- The compiled flat overlay equals sequential single-key patching exactly,
not merely sampled result equality. No factory is evaluated during compilation. -/
theorem ProviderOverlay.compile_provider (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) :
    (compile base edits).provider = edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) base := by
  exact fold_set_provider edits (ofProvider base)

/-- Whole consumer preparations retain exact dependent factories and first errors. -/
theorem Requirements.prepare_overlay_set (overlay : ProviderOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) (keys : List Key) :
    prepare (overlay.set key replacement).provider keys =
      prepare (overlay.provider.patchKey key replacement) keys := by
  rw [ProviderOverlay.set_provider]

theorem Requirements.prepare_overlay_compile (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key) :
    prepare (ProviderOverlay.compile base edits).provider keys =
      prepare (edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) base) keys := by
  rw [ProviderOverlay.compile_provider]

end LeanPoo.Functional
