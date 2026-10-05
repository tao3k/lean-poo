import LeanPoo.Functional.IndexedTransaction

/-! Optional name-only transaction preflight against an immutable registry. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Check names in caller order, including empty batches. No edit cells, factory
bodies or update tables are traversed/constructed. Successful preflight says only
that names are registered; it does not establish capability availability. -/
def checkTransactionNames (contains : String → Bool) :
    List (RegistryEdit Context Key Value) → Except String Unit
  | [] => .ok ()
  | edit :: rest => if contains edit.1 then checkTransactionNames contains rest else .error edit.1

/-- Preflight an ordinary registry without constructing intermediate updates. -/
def ProviderRegistry.checkTransaction (registry : ProviderRegistry Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) : Except String Unit :=
  checkTransactionNames registry.entries.contains edits

/-- The same preflight for retained indexed state; no snapshot materialization. -/
def IndexedRegistry.checkTransaction [BEq Key] [Hashable Key]
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    Except String Unit := checkTransactionNames registry.entries.contains edits

/-- Success means every named batch targets the initial registry's scope. -/
theorem checkTransactionNames_ok_iff (contains : String → Bool)
    (edits : List (RegistryEdit Context Key Value)) :
    checkTransactionNames contains edits = .ok () ↔ ∀ edit ∈ edits, contains edit.1 = true := by
  induction edits with
  | nil => simp [checkTransactionNames]
  | cons edit rest ih =>
    cases known : contains edit.1 <;> simp [checkTransactionNames, known, ih]

/-- Scope agreement suffices to reuse a preflight, regardless of provider values. -/
theorem checkTransactionNames_congr (left right : String → Bool)
    (edits : List (RegistryEdit Context Key Value)) (same : ∀ name, left name = right name) :
    checkTransactionNames left edits = checkTransactionNames right edits := by
  rw [funext same]

/-- Exact first-error agreement, not merely success equivalence. Name membership
is preserved by every successful batch, so preflight reads the initial scope. -/
theorem ProviderRegistry.checkTransaction_outcome [DecidableEq Key]
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    registry.checkTransaction edits = (registry.patchTransaction edits).map (fun _ => ()) := by
  induction edits generalizing registry with
  | nil => rfl
  | cons edit rest ih =>
    cases found : registry.entries[edit.1]? with
    | none =>
      simp [checkTransaction, checkTransactionNames, Std.HashMap.contains_eq_isSome_getElem?,
        found, patchTransaction, patchBatch, Except.map]
      rfl
    | some provider =>
      let next : ProviderRegistry Context Key Value :=
        ⟨registry.entries.insert edit.1 (ProviderOverlay.compile provider edit.2).provider⟩
      have step : registry.patchBatch edit.1 edit.2 = .ok next := by simp [patchBatch, found, next]
      have scope : next.entries.contains = registry.entries.contains := by
        funext name
        exact patchBatch_scope registry edit.1 edit.2 step
      have tail := ih next
      rw [checkTransaction, scope] at tail
      simpa only [checkTransaction, checkTransactionNames, Std.HashMap.contains_eq_isSome_getElem?,
        found, Option.isSome_some, Bool.true_eq, ↓reduceIte, patchTransaction_cons, step,
        Except.bind] using tail

theorem IndexedRegistry.checkTransaction_outcome [BEq Key] [Hashable Key]
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    registry.checkTransaction edits = (registry.patchTransaction edits).map (fun _ => ()) := by
  induction edits generalizing registry with
  | nil => rfl
  | cons edit rest ih =>
    cases found : registry.entries[edit.1]? with
    | none =>
      simp [checkTransaction, checkTransactionNames, Std.HashMap.contains_eq_isSome_getElem?,
        found, patchTransaction, patchBatch, Except.map]
      rfl
    | some state =>
      let next : IndexedRegistry Context Key Value := ⟨registry.entries.insert edit.1 (state.extend edit.2)⟩
      have step : registry.patchBatch edit.1 edit.2 = .ok next := by simp [patchBatch, found, next]
      have scope : next.entries.contains = registry.entries.contains := by
        funext name
        exact patchBatch_scope registry edit.1 edit.2 step
      have tail := ih next
      rw [checkTransaction, scope] at tail
      simpa only [checkTransaction, checkTransactionNames, Std.HashMap.contains_eq_isSome_getElem?,
        found, Option.isSome_some, Bool.true_eq, ↓reduceIte, patchTransaction_cons, step,
        Except.bind] using tail

/-- A successful update transaction preserves preflight results for any future
plan. The immutable original scope is enough; no per-name caller proof is needed. -/
theorem ProviderRegistry.checkTransaction_after [DecidableEq Key]
    (registry updated : ProviderRegistry Context Key Value) (changes pending : List (RegistryEdit Context Key Value))
    (applied : registry.patchTransaction changes = .ok updated) :
    updated.checkTransaction pending = registry.checkTransaction pending :=
  checkTransactionNames_congr _ _ pending (fun _ => patchTransaction_scope registry changes applied)

theorem IndexedRegistry.checkTransaction_after [BEq Key] [Hashable Key]
    (registry updated : IndexedRegistry Context Key Value) (changes pending : List (RegistryEdit Context Key Value))
    (applied : registry.patchTransaction changes = .ok updated) :
    updated.checkTransaction pending = registry.checkTransaction pending :=
  checkTransactionNames_congr _ _ pending (fun _ => patchTransaction_scope registry changes applied)

/-- Conversion preserves name checks directly, without materializing a snapshot. -/
theorem IndexedRegistry.ofRegistry_checkTransaction [BEq Key] [Hashable Key]
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    (ofRegistry registry).checkTransaction edits = registry.checkTransaction edits := by
  apply checkTransactionNames_congr
  intro name
  simp only [ofRegistry, Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_map]
  cases registry.entries[name]? <;> rfl

end LeanPoo.Functional
