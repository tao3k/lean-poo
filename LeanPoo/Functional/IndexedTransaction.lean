import LeanPoo.Functional.IndexedRegistry
import LeanPoo.Functional.RegistryTransaction

/-! Atomic named transactions on retained indexed state. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- Caller-order batches with first-error propagation. No successful prefix is
returned on failure. Repeated names extend retained state without new base wrappers;
no full-table snapshot or factory execution is required. -/
def IndexedRegistry.patchTransaction (registry : IndexedRegistry Context Key Value) :
    List (RegistryEdit Context Key Value) → Except String (IndexedRegistry Context Key Value)
  | [] => .ok registry
  | edit :: rest => do
    let next ← registry.patchBatch edit.1 edit.2
    next.patchTransaction rest

omit [LawfulBEq Key] [DecidableEq Key] in
@[simp] theorem IndexedRegistry.patchTransaction_nil (registry : IndexedRegistry Context Key Value) :
    registry.patchTransaction [] = .ok registry := rfl

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.patchTransaction_cons (registry : IndexedRegistry Context Key Value)
    (edit : RegistryEdit Context Key Value) (rest : List (RegistryEdit Context Key Value)) :
    registry.patchTransaction (edit :: rest) =
      (registry.patchBatch edit.1 edit.2).bind (fun next => next.patchTransaction rest) := rfl

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.patchTransaction_missing (registry : IndexedRegistry Context Key Value)
    (edit : RegistryEdit Context Key Value) (rest : List (RegistryEdit Context Key Value))
    (absent : registry.entries[edit.1]? = none) :
    registry.patchTransaction (edit :: rest) = .error edit.1 := by
  rw [patchTransaction_cons, patchBatch_missing registry edit.1 edit.2 absent]
  rfl

omit [LawfulBEq Key] [DecidableEq Key] in
/-- All original per-name bases remain fixed, including repeated-name updates. -/
theorem IndexedRegistry.patchTransaction_base (registry : IndexedRegistry Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) (target : String)
    (applied : registry.patchTransaction edits = .ok updated) :
    (updated.entries[target]?).map (fun state : IndexedOverlay Context Key Value => state.base) =
      (registry.entries[target]?).map (fun state : IndexedOverlay Context Key Value => state.base) := by
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
      exact (ih next tail).trans (patchBatch_base registry edit.1 target edit.2 step)

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.patchTransaction_scope (registry : IndexedRegistry Context Key Value)
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

/-- One rewrite reuses the whole prepared consumer after successful transactions
outside its ancestor/key read scope. Negative scope never suppresses name errors. -/
theorem Requirements.prepare_indexedTransaction_of_unaffected (index : C4.AncestryIndex graph root)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
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
      rw [IndexedRegistry.patchTransaction_cons, step] at applied
      contradiction
    | ok next =>
      have tail : next.patchTransaction rest = .ok updated := by
        rw [IndexedRegistry.patchTransaction_cons, step] at applied
        exact applied
      exact (ih next tail scopes.2).trans
        (prepare_indexedRegistry_of_unaffected index registry edit.1 edit.2 keys step scopes.1)

end LeanPoo.Functional
