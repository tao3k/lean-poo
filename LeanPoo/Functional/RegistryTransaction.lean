import LeanPoo.Functional.RegistryBatch

/-! Pure transactions spanning named provider batches. No partial registry is
returned on failure; the caller's original snapshot remains available. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

abbrev RegistryEdit (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) :=
  String × List (CapabilityEdit Context Key Value)

/-- Execute in caller order, returning the first unknown name or the completed
snapshot. Repeated names are sequential; this does not group/flatten their bases.
Each reached batch performs one lookup and, on success, one insertion. -/
def ProviderRegistry.patchTransaction (registry : ProviderRegistry Context Key Value) :
    List (RegistryEdit Context Key Value) → Except String (ProviderRegistry Context Key Value)
  | [] => .ok registry
  | edit :: rest => do
    let next ← registry.patchBatch edit.1 edit.2
    next.patchTransaction rest

@[simp] theorem ProviderRegistry.patchTransaction_nil (registry : ProviderRegistry Context Key Value) :
    registry.patchTransaction [] = .ok registry := rfl

/-- Bind law exposes exact sequencing and first-error propagation. -/
theorem ProviderRegistry.patchTransaction_cons (registry : ProviderRegistry Context Key Value)
    (edit : RegistryEdit Context Key Value) (rest : List (RegistryEdit Context Key Value)) :
    registry.patchTransaction (edit :: rest) =
      (registry.patchBatch edit.1 edit.2).bind (fun next => next.patchTransaction rest) := rfl

theorem ProviderRegistry.patchTransaction_missing (registry : ProviderRegistry Context Key Value)
    (edit : RegistryEdit Context Key Value) (rest : List (RegistryEdit Context Key Value))
    (absent : registry.entries[edit.1]? = none) :
    registry.patchTransaction (edit :: rest) = .error edit.1 := by
  rw [patchTransaction_cons, patchBatch_missing registry edit.1 edit.2 absent]
  rfl

/-- Successful transactions preserve the complete provider-name membership. -/
theorem ProviderRegistry.patchTransaction_scope (registry : ProviderRegistry Context Key Value)
    (edits : List (RegistryEdit Context Key Value))
    (applied : registry.patchTransaction edits = .ok updated) :
    updated.entries.contains target = registry.entries.contains target := by
  induction edits generalizing registry with
  | nil => cases applied; rfl
  | cons edit rest ih =>
    cases step : registry.patchBatch edit.1 edit.2 with
    | error name =>
      rw [patchTransaction_cons, step] at applied
      contradiction
    | ok next =>
      have tail : next.patchTransaction rest = .ok updated := by
        rw [patchTransaction_cons, step] at applied
        exact applied
      exact (ih next tail).trans (patchBatch_scope registry edit.1 edit.2 step)

/-- Conservative union of named batch read-scope candidates; empty is false. -/
def Requirements.transactionMayAffect (index : C4.AncestryIndex graph root) (keys : List Key)
    (edits : List (RegistryEdit Context Key Value)) : Bool :=
  edits.any (fun edit => batchMayAffect index keys edit.1 edit.2)

theorem Requirements.transactionMayAffect_iff (index : C4.AncestryIndex graph root) (keys : List Key)
    (edits : List (RegistryEdit Context Key Value)) :
    transactionMayAffect index keys edits = true ↔
      ∃ edit ∈ edits, C4.Ancestor graph edit.1 root ∧ ∃ cell ∈ edit.2, cell.1 ∈ keys := by
  simp [transactionMayAffect, batchMayAffect_iff]

/-- One whole-consumer rewrite covers arbitrarily many named changes, all
contexts, repeated keys and first missing-key errors. No per-name alignment is
required. Success is explicit: a negative read scope does not suppress errors. -/
theorem Requirements.prepare_patchTransaction_of_unaffected (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (keys : List Key) (applied : registry.patchTransaction edits = .ok updated)
    (unaffected : transactionMayAffect index keys edits = false) :
    prepare (assemble index.order updated.dictionary) keys =
      prepare (assemble index.order registry.dictionary) keys := by
  induction edits generalizing registry with
  | nil => cases applied; rfl
  | cons edit rest ih =>
    have scopes : batchMayAffect index keys edit.1 edit.2 = false ∧
        transactionMayAffect index keys rest = false := by
      simpa [transactionMayAffect] using unaffected
    cases step : registry.patchBatch edit.1 edit.2 with
    | error name =>
      rw [ProviderRegistry.patchTransaction_cons, step] at applied
      contradiction
    | ok next =>
      have tail : next.patchTransaction rest = .ok updated := by
        rw [ProviderRegistry.patchTransaction_cons, step] at applied
        exact applied
      exact (ih next tail scopes.2).trans
        (prepare_patchBatch_of_unaffected index registry edit.1 edit.2 keys step scopes.1)

end LeanPoo.Functional
