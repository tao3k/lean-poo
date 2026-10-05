import LeanPoo.Functional.ScopedTransaction
import Std.Data.HashSet.Lemmas

/-! Retain a verified requested-key set for repeated transaction impact checks. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key}

/-- Runtime hash set tied to the exact requested list. Duplicates/order remain in
that list for preparation; only impact membership is indexed. Proof is erased. -/
structure KeyIndex (keys : List Key) [BEq Key] [Hashable Key] where
  entries : Std.HashSet Key
  indexed : ∀ key, entries.contains key = true ↔ key ∈ keys

/-- Build once and retain across many change sets. No provider/factory executes. -/
def KeyIndex.ofKeys [BEq Key] [Hashable Key] [LawfulBEq Key] (keys : List Key) : KeyIndex keys :=
  ⟨Std.HashSet.ofList keys, by intro key; simp⟩

def KeyIndex.contains [BEq Key] [Hashable Key] (index : KeyIndex keys) (key : Key) : Bool :=
  index.entries.contains key

theorem KeyIndex.contains_iff [BEq Key] [Hashable Key] (index : KeyIndex keys) (key : Key) :
    index.contains key = true ↔ key ∈ keys := index.indexed key

theorem KeyIndex.contains_eq [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]
    (index : KeyIndex keys) (key : Key) : index.contains key = decide (key ∈ keys) := by
  have membership := index.contains_iff key
  cases found : index.contains key <;> by_cases present : key ∈ keys <;> simp_all

variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- One hash membership probe per reached cell instead of scanning requested
keys. The raw edit history is still scanned until the first overlap. -/
def batchMayAffectIndexed (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (name : String) (edits : List (CapabilityEdit Context Key Value)) : Bool :=
  index.isAncestor name && edits.any (fun edit => scope.contains edit.1)

def transactionMayAffectIndexed (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (edits : List (RegistryEdit Context Key Value)) : Bool :=
  edits.any (fun edit => batchMayAffectIndexed index scope edit.1 edit.2)

omit [LawfulBEq Key] in
theorem batchMayAffectIndexed_eq (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (name : String) (edits : List (CapabilityEdit Context Key Value)) :
    batchMayAffectIndexed index scope name edits = batchMayAffect index keys name edits := by
  unfold batchMayAffectIndexed batchMayAffect
  apply congrArg (fun predicate : CapabilityEdit Context Key Value → Bool => index.isAncestor name && edits.any predicate)
  funext edit
  apply Bool.eq_iff_iff.mpr
  simpa using scope.contains_iff edit.1

omit [LawfulBEq Key] in
theorem transactionMayAffectIndexed_eq (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (edits : List (RegistryEdit Context Key Value)) :
    transactionMayAffectIndexed index scope edits = transactionMayAffect index keys edits := by
  simp only [transactionMayAffectIndexed, transactionMayAffect, batchMayAffectIndexed_eq]

/-- Same consumer-only fast path with a retained requested-key index. Index
construction is separate; positive fallback, name checks and query costs remain. -/
def prepareTransactionIndexed (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    Except String (Except Key (Factories Context Value keys)) :=
  if transactionMayAffectIndexed index scope edits then
    (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys)
  else (registry.checkTransaction edits).map (fun _ => prepare (assemble index.order registry.dictionary) keys)

theorem prepareTransactionIndexed_eq (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : IndexedRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    prepareTransactionIndexed index scope registry edits = prepareTransaction index registry edits keys := by
  simp only [prepareTransactionIndexed, prepareTransaction, transactionMayAffectIndexed_eq]

theorem prepareTransactionIndexed_ofRegistry (index : C4.AncestryIndex graph root) (scope : KeyIndex keys)
    (registry : ProviderRegistry Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    prepareTransactionIndexed index scope (IndexedRegistry.ofRegistry registry) edits =
      (registry.patchTransaction edits).map (fun updated => prepare (assemble index.order updated.dictionary) keys) := by
  rw [prepareTransactionIndexed_eq, prepareTransaction_ofRegistry]

end LeanPoo.Functional.Requirements
