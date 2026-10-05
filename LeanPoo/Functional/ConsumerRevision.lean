import LeanPoo.Functional.CachedPreparation

/-! Publish the full immutable transaction state and automatically align retained
consumer certificates; fresh results can be certified without preparing twice. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}

/-- Exact complete prepared data/error bound to one provider, without a claim. -/
structure Prepared (provider : Provider Context Key Value) (keys : List Key) where
  outcome : Except Key (Factories Context Value keys)
  aligned : outcome = prepare provider keys

private def certifyOutcome (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop)
    (outcome : Except Key (Factories Context Value keys))
    (aligned : outcome = prepare provider keys)
    (admit : ∀ f, Selected provider keys f → ∀ c, Claim c (build f c)) :
    Except Key (Certified keys Claim) :=
  match outcome with
  | .error key => .error key
  | .ok f => .ok ⟨f, admit f ((prepare_ok_iff _ _ _).mp aligned.symm)⟩

private theorem certifyOutcome_forget (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop)
    (outcome : Except Key (Factories Context Value keys))
    (aligned : outcome = prepare provider keys)
    (admit : ∀ f, Selected provider keys f → ∀ c, Claim c (build f c)) :
    (certifyOutcome provider keys Claim outcome aligned admit).map Certified.factories = outcome := by
  unfold certifyOutcome
  split <;> rename_i ready <;> simp [Except.map, ready]

/-- Admit the already prepared outcome without another provider lookup. The
new joint analytic proof must be supplied for the exact new provider. -/
def Prepared.certify {provider : Provider Context Key Value}
    (saved : Prepared provider keys) (Claim : ∀ c, Results Value c keys → Prop)
    (admit : ∀ f, Selected provider keys f → ∀ c, Claim c (build f c)) :
    CachedPreparation provider keys Claim :=
  ⟨certifyOutcome provider keys Claim saved.outcome saved.aligned admit,
    (certifyOutcome_forget provider keys Claim saved.outcome saved.aligned admit).trans saved.aligned⟩

theorem Prepared.certify_forget {provider : Provider Context Key Value}
    (saved : Prepared provider keys) (Claim : ∀ c, Results Value c keys → Prop)
    (admit : ∀ f, Selected provider keys f → ∀ c, Claim c (build f c)) :
    (saved.certify Claim admit).outcome.map Certified.factories = saved.outcome :=
  certifyOutcome_forget provider keys Claim saved.outcome saved.aligned admit

/-- Rebind a retained success/error and joint proof using exact preparation
agreement. Only its erased alignment changes; no query or admission runs. -/
def CachedPreparation.rebind {provider : Provider Context Key Value}
    (cache : CachedPreparation provider keys Claim) (other : Provider Context Key Value)
    (same : prepare other keys = prepare provider keys) : CachedPreparation other keys Claim :=
  ⟨cache.outcome, cache.aligned.trans same.symm⟩

@[simp] theorem CachedPreparation.rebind_outcome {provider : Provider Context Key Value}
    (cache : CachedPreparation provider keys Claim) (other : Provider Context Key Value)
    (same : prepare other keys = prepare provider keys) :
    (cache.rebind other same).outcome = cache.outcome := rfl

variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- Both branches publish the full updated registry. Reused carries a cache
aligned to it; fresh carries exact prepared data awaiting new proof admission. -/
inductive ConsumerRevision (index : C4.AncestryIndex graph root) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop) where
  | reused (registry : IndexedRegistry Context Key Value)
      (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim)
  | fresh (registry : IndexedRegistry Context Key Value)
      (prepared : Prepared (assemble index.order registry.dictionary) keys)

def ConsumerRevision.registry (revision : ConsumerRevision index keys Claim) :
    IndexedRegistry Context Key Value := match revision with
  | .reused registry _ => registry
  | .fresh registry _ => registry

def ConsumerRevision.forget (revision : ConsumerRevision index keys Claim) :
    Except Key (Factories Context Value keys) := match revision with
  | .reused _ cache => cache.outcome.map Certified.factories
  | .fresh _ prepared => prepared.outcome

/-- Newly certified results remain tied to the registry returned by this
revision. Reused does not call admission; fresh does not repeat preparation. -/
def ConsumerRevision.certify (revision : ConsumerRevision index keys Claim)
    (admit : ∀ f, Selected (assemble index.order revision.registry.dictionary) keys f →
      ∀ c, Claim c (build f c)) :
    CachedPreparation (assemble index.order revision.registry.dictionary) keys Claim :=
  match revision with
  | .reused _ cache => cache
  | .fresh _ prepared => prepared.certify Claim admit

omit [DecidableEq Key] in
theorem ConsumerRevision.certify_forget (revision : ConsumerRevision index keys Claim)
    (admit : ∀ f, Selected (assemble index.order revision.registry.dictionary) keys f →
      ∀ c, Claim c (build f c)) :
    (revision.certify admit).outcome.map Certified.factories = revision.forget := by
  cases revision with
  | reused registry cache => rfl
  | fresh registry prepared => exact prepared.certify_forget Claim admit


/-- Full transaction publication. Unknown names return no updated prefix.
Negative impact automatically rebinds the old certified outcome to the new
registry; positive impact prepares fresh data without reusing the old proof. -/
def applyTransactionCached (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim) :
    Except String (ConsumerRevision index keys Claim) :=
  match applied : registry.patchTransaction edits with
  | .error name => .error name
  | .ok updated =>
    if impact : transactionMayAffectIndexed index scope edits then
      .ok (.fresh updated ⟨prepare (assemble index.order updated.dictionary) keys, rfl⟩)
    else .ok (.reused updated (cache.rebind _
      (prepare_indexedTransaction_of_unaffected index registry edits keys applied
        (by rw [← transactionMayAffectIndexed_eq index scope edits];
            cases found : transactionMayAffectIndexed index scope edits <;> simp_all))))

/-- Full returned registry equality, including exact first transaction errors. -/
theorem applyTransactionCached_registry (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim) :
    (applyTransactionCached index scope registry edits cache).map ConsumerRevision.registry =
      registry.patchTransaction edits := by
  unfold applyTransactionCached
  split
  · rename_i applied; simp [Except.map, applied]
  · rename_i updated applied
    split <;> simp [Except.map, ConsumerRevision.registry, applied]

/-- Complete consumer equality from the published state, including first-key
errors and functions at every future context; no manual cache alignment. -/
theorem applyTransactionCached_forget (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order registry.dictionary) keys Claim) :
    (applyTransactionCached index scope registry edits cache).map ConsumerRevision.forget =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  unfold applyTransactionCached
  split
  · rename_i applied; simp [Except.map, applied]
  · rename_i updated applied
    split
    · simp [Except.map, ConsumerRevision.forget, applied]
    · rename_i unaffected
      simp only [Except.map, ConsumerRevision.forget, CachedPreparation.rebind_outcome]
      rw [applied]
      change Except.ok (cache.outcome.map Certified.factories) =
        Except.ok (prepare (assemble index.order updated.dictionary) keys)
      rw [prepare_indexedTransaction_of_unaffected index registry edits keys applied
        (by rw [← transactionMayAffectIndexed_eq index scope edits];
            cases found : transactionMayAffectIndexed index scope edits <;> simp_all)]
      rw [cache.aligned]

/-- Ordinary storage conversion supplies complete consumer agreement. -/
theorem applyTransactionCached_ofRegistry (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (cache : CachedPreparation (assemble index.order (IndexedRegistry.ofRegistry registry).dictionary) keys Claim) :
    (applyTransactionCached index scope (IndexedRegistry.ofRegistry registry) edits cache).map ConsumerRevision.forget =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  rw [applyTransactionCached_forget]
  exact IndexedRegistry.ofRegistry_transaction_consumer registry edits
    (fun dictionary => prepare (assemble index.order dictionary) keys)

end LeanPoo.Functional.Requirements
