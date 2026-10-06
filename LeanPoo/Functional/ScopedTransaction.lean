import LeanPoo.Functional.TransactionCheck

/-! Prepare a consumer's transaction view without constructing irrelevant updates. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- Consumer-only transaction preparation. Conservative positive impact takes the
full update path. Negative impact checks all names, then retains the original
prepared functions without constructing update prefixes. No factory executes.
This returns a view, not an updated registry to publish. -/
def prepareTransaction (index : C4.AncestryIndex graph root)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (keys : List Key) : Except String (Except Key (Factories Context Value keys)) :=
  if transactionMayAffect index keys edits then
    (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys)
  else registry.checkTransaction edits |>.map (fun _ => prepare (assemble index.order registry.dictionary) keys)

/-- Exact full-path semantics, including transaction first-name errors, capability
first-key errors, repeated requested keys and all future contexts. -/
theorem prepareTransaction_eq (index : C4.AncestryIndex graph root)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (keys : List Key) :
    prepareTransaction index registry edits keys =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  unfold prepareTransaction
  split
  · rfl
  · rename_i negative
    have unaffected : transactionMayAffect index keys edits = false := by
      cases impact : transactionMayAffect index keys edits <;> simp_all
    rw [IndexedRegistry.checkTransaction_outcome]
    cases applied : registry.patchTransaction edits with
    | error name => rfl
    | ok updated =>
      simp only [Except.map]
      rw [prepare_indexedTransaction_of_unaffected index registry edits keys applied unaffected]

/-- Storage conversion also preserves the complete scoped consumer view. No
caller alignment, successful-transaction or negative-impact premise is needed. -/
theorem prepareTransaction_ofRegistry (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (keys : List Key) :
    prepareTransaction index (IndexedRegistry.ofRegistry registry) edits keys =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  rw [prepareTransaction_eq]
  exact IndexedRegistry.ofRegistry_transaction_consumer registry edits
    (fun dictionary => prepare (assemble index.order dictionary) keys)

/-- Negative scope preserves name errors while avoiding all update construction. -/
theorem prepareTransaction_unaffected (index : C4.AncestryIndex graph root)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (keys : List Key) (unaffected : transactionMayAffect index keys edits = false) :
    prepareTransaction index registry edits keys =
      (registry.checkTransaction edits).map (fun _ => prepare (assemble index.order registry.dictionary) keys) := by
  simp [prepareTransaction, unaffected]

end LeanPoo.Functional.Requirements
