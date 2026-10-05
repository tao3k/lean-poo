import LeanPoo.Functional.IndexedRegistry
import LeanPoo.Functional.RegistryTransaction

/-! Atomic named transactions on retained indexed state. -/
namespace LeanPoo.Functional
universe u v w x
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

/-- Exact transaction outcomes across representations. Dictionary agreement alone
cannot distinguish an absent name from a registered empty provider, so name scope
is an explicit premise. Covers affected consumers and first unknown-name errors. -/
theorem IndexedRegistry.patchTransaction_congr (registry : IndexedRegistry Context Key Value)
    (ordinary : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (agreement : registry.dictionary = ordinary.dictionary)
    (scope : ∀ target, registry.entries.contains target = ordinary.entries.contains target) :
    (registry.patchTransaction edits).map IndexedRegistry.dictionary =
      (ordinary.patchTransaction edits).map ProviderRegistry.dictionary := by
  induction edits generalizing registry ordinary with
  | nil => simp [patchTransaction, ProviderRegistry.patchTransaction, Except.map, agreement]
  | cons edit rest ih =>
    cases found : registry.entries[edit.1]? with
    | none =>
      have absent : ordinary.entries[edit.1]? = none := by
        have names := scope edit.1
        simp only [Std.HashMap.contains_eq_isSome_getElem?, found, Option.isSome_none] at names
        cases other : ordinary.entries[edit.1]? <;> simp_all
      simp [patchTransaction, patchBatch, ProviderRegistry.patchTransaction,
        ProviderRegistry.patchBatch, found, absent, Except.map]
      rfl
    | some state =>
      cases other : ordinary.entries[edit.1]? with
      | none =>
        have names := scope edit.1
        simp [Std.HashMap.contains_eq_isSome_getElem?, found, other] at names
      | some provider =>
        let next : IndexedRegistry Context Key Value :=
          ⟨registry.entries.insert edit.1 (state.extend edit.2)⟩
        let reference : ProviderRegistry Context Key Value :=
          ⟨ordinary.entries.insert edit.1 (ProviderOverlay.compile provider edit.2).provider⟩
        have step : registry.patchBatch edit.1 edit.2 = .ok next := by
          simp [patchBatch, found, next]
        have control : ordinary.patchBatch edit.1 edit.2 = .ok reference := by
          simp [ProviderRegistry.patchBatch, other, reference]
        have dictionaries : next.dictionary = reference.dictionary := by
          funext target
          by_cases same : target = edit.1
          · subst target
            rw [patchBatch_at registry edit.1 edit.2 step,
              ProviderRegistry.patchBatch_at ordinary edit.1 edit.2 control, agreement]
          · rw [patchBatch_other registry edit.1 edit.2 step same,
              ProviderRegistry.patchBatch_other ordinary edit.1 edit.2 control same, agreement]
        have names : ∀ target, next.entries.contains target = reference.entries.contains target := by
          intro target
          exact (patchBatch_scope registry edit.1 edit.2 step).trans
            ((scope target).trans (ProviderRegistry.patchBatch_scope ordinary edit.1 edit.2 control).symm)
        simpa only [patchTransaction_cons, ProviderRegistry.patchTransaction_cons, step, control,
          Except.bind] using ih next reference dictionaries names

/-- Convert once; all subsequent transaction outcomes have ordinary semantics.
No comparison snapshot, per-name alignment or negative-impact premise is needed. -/
theorem IndexedRegistry.ofRegistry_patchTransaction (ordinary : ProviderRegistry Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) :
    ((ofRegistry ordinary).patchTransaction edits).map IndexedRegistry.dictionary =
      (ordinary.patchTransaction edits).map ProviderRegistry.dictionary := by
  apply patchTransaction_congr _ _ _ (ofRegistry_dictionary ordinary)
  intro target
  simp only [ofRegistry, Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_map]
  cases ordinary.entries[target]? <;> rfl

/-- Transfer any dictionary consumer, retaining both transaction errors and the
consumer's own result/error semantics. Factory execution is entirely caller-owned. -/
theorem IndexedRegistry.ofRegistry_transaction_consumer {Result : Type x}
    (ordinary : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (consume : (String → Provider Context Key Value) → Result) :
    ((ofRegistry ordinary).patchTransaction edits).map (fun updated => consume updated.dictionary) =
      (ordinary.patchTransaction edits).map (fun updated => consume updated.dictionary) := by
  have outcomes := congrArg (fun result => result.map consume) (ofRegistry_patchTransaction ordinary edits)
  cases indexed : (ofRegistry ordinary).patchTransaction edits <;>
    cases control : ordinary.patchTransaction edits <;>
    simpa only [indexed, control, Except.map] using outcomes

end LeanPoo.Functional
