import LeanPoo.Functional.CertifiedRequirements
import LeanPoo.Functional.KeyIndex

/-! Retain exact prepared outcomes and joint certificates across scope-negative
transactions. Positive impact prepares fresh data, requiring fresh admission. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}

/-- Bind a cached success or first capability error to the exact provider view.
Alignment is a proof, erased along with joint certificate fields. -/
structure CachedPreparation (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop) where
  outcome : Except Key (Certified keys Claim)
  aligned : outcome.map Certified.factories = prepare provider keys

/-- Prepare once; cache both success and failure, preserving exact diagnostics. -/
def cacheCertified (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop)
    (admit : ∀ factories, Selected provider keys factories →
      ∀ c, Claim c (build factories c)) : CachedPreparation provider keys Claim :=
  ⟨prepareCertified provider keys Claim admit, prepareCertified_forget provider keys Claim admit⟩

/-- Reused results retain the old joint proof. Fresh data has no joint proof
until the caller supplies one; overlap alone is not evidence of invalidity. -/
inductive TransactionPreparation (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop) where
  | reused : Except Key (Certified keys Claim) → TransactionPreparation keys Claim
  | fresh : Except Key (Factories Context Value keys) → TransactionPreparation keys Claim

/-- Erase the reuse decision and certificates, preserving complete data/errors. -/
def TransactionPreparation.forget : TransactionPreparation keys Claim →
    Except Key (Factories Context Value keys)
  | .reused outcome => outcome.map Certified.factories
  | .fresh outcome => outcome

variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- Negative scope checks all names, then returns the cached tuple/error directly:
no provider selection, preparation, update construction or factory execution.
Positive scope follows the full update/preparation path without reusing proofs.
This is a consumer view, not updated registry publication. -/
def prepareTransactionCached (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim) :
    Except String (TransactionPreparation keys Claim) :=
  if transactionMayAffectIndexed index scope edits then
    (registry.patchTransaction edits).map (fun updated =>
      .fresh (prepare (assemble index.order updated.dictionary) keys))
  else (registry.checkTransaction edits).map (fun _ => .reused cache.outcome)

/-- Arbitrary cached joint contracts preserve full-path data and error semantics.
No analytic premise about edited providers is inferred from the old certificate. -/
theorem prepareTransactionCached_forget (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim) :
    (prepareTransactionCached index scope registry edits cache).map TransactionPreparation.forget =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  rw [← prepareTransaction_eq index registry edits keys, ← prepareTransactionIndexed_eq index scope registry edits]
  unfold prepareTransactionCached prepareTransactionIndexed
  split
  · cases registry.patchTransaction edits <;> rfl
  · cases registry.checkTransaction edits with
    | error name => rfl
    | ok ignored =>
      change Except.ok (cache.outcome.map Certified.factories) = Except.ok _
      rw [cache.aligned]

/-- Exact ordinary-registry consumer semantics after storage conversion. -/
theorem prepareTransactionCached_ofRegistry (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order (IndexedRegistry.ofRegistry registry).dictionary) keys Claim) :
    (prepareTransactionCached index scope (IndexedRegistry.ofRegistry registry) edits cache).map TransactionPreparation.forget =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  rw [prepareTransactionCached_forget]
  exact IndexedRegistry.ofRegistry_transaction_consumer registry edits
    (fun dictionary => prepare (assemble index.order dictionary) keys)

omit [DecidableEq Key] in
/-- Negative scope returns the original entire certificate/error, after names. -/
theorem prepareTransactionCached_unaffected (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim)
    (unaffected : transactionMayAffectIndexed index scope edits = false) :
    prepareTransactionCached index scope registry edits cache =
      (registry.checkTransaction edits).map (fun _ => .reused cache.outcome) := by
  simp [prepareTransactionCached, unaffected]

omit [DecidableEq Key] in
/-- Conservative overlap never silently reuses the old joint proof. -/
theorem prepareTransactionCached_affected (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim)
    (affected : transactionMayAffectIndexed index scope edits = true) :
    prepareTransactionCached index scope registry edits cache =
      (registry.patchTransaction edits).map (fun updated =>
        .fresh (prepare (assemble index.order updated.dictionary) keys)) := by
  simp [prepareTransactionCached, affected]

end LeanPoo.Functional.Requirements
