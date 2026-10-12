import LeanPoo.Functional.Absence
import LeanPoo.Functional.RegistryTransaction

/-! Preserve explicit negative assumptions when extending existing providers.
The graph and key family are fixed; candidate snapshots remain immutable. -/
namespace LeanPoo.Functional

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- Scope-negative transactions preserve every requested selection, including
all absent keys after the first one. Checklist first-error equality alone
would not establish that stronger negative contract. -/
theorem assemble_transaction_stable (index : C4.AncestryIndex graph root)
    (registry updated : ProviderRegistry Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchTransaction edits = .ok updated)
    (unaffected : Requirements.transactionMayAffect index keys edits = false)
    (key : Key) (requested : key ∈ keys) :
    assemble index.order updated.dictionary key = assemble index.order registry.dictionary key := by
  have singleton : Requirements.transactionMayAffect index [key] edits = false := by
    cases impact : Requirements.transactionMayAffect index [key] edits with
    | false => rfl
    | true =>
      obtain ⟨edit, included, ancestor, cell, member, same⟩ :=
        (Requirements.transactionMayAffect_iff index [key] edits).mp impact
      have equal : cell.1 = key := by simpa using same
      have forbidden := (Requirements.transactionMayAffect_iff index keys edits).mpr
        ⟨edit, included, ancestor, cell, member, equal ▸ requested⟩
      simp [unaffected] at forbidden
  have preserved := Requirements.prepare_patchTransaction_of_unaffected
    index registry edits [key] applied singleton
  cases old : assemble index.order registry.dictionary key <;>
    cases fresh : assemble index.order updated.dictionary key <;>
    simp_all [Requirements.prepare]
  injection preserved with pair
  exact congrArg Prod.fst pair

structure AbsenceRevision (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (keys : List Key)
    (edits : List (RegistryEdit Context Key Value)) where
  snapshot : ProviderRegistry Context Key Value
  applied : registry.patchTransaction edits = .ok snapshot
  certificate : Requirements.AbsenceCertificate (assemble index.order snapshot.dictionary) keys

/-- Refusals retain either the exact first name error or the completed candidate
and its first present capability. They are evidence, not an accepted revision. -/
inductive AbsenceExtensionFailure (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (keys : List Key)
    (edits : List (RegistryEdit Context Key Value)) where
  | unknownProvider (name : String) (failed : registry.patchTransaction edits = .error name)
  | introduced (candidate : ProviderRegistry Context Key Value)
      (applied : registry.patchTransaction edits = .ok candidate)
      (conflict : Requirements.Presence (assemble index.order candidate.dictionary) keys)

/-- Apply the whole pure transaction before checking the old negative contract.
On disjoint scope, reuse its proof with exact selection preservation. On overlap,
check actual availability: removal/overwrite may still preserve absence.
Factories never execute. An unknown name is reported before absence conflicts. -/
def guardAbsenceTransaction (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (keys : List Key)
    (certificate : Requirements.AbsenceCertificate (assemble index.order registry.dictionary) keys)
    (edits : List (RegistryEdit Context Key Value)) :
    Except (AbsenceExtensionFailure index registry keys edits) (AbsenceRevision index registry keys edits) :=
  match applied : registry.patchTransaction edits with
  | .error name => .error (.unknownProvider name applied)
  | .ok candidate =>
    if unaffected : Requirements.transactionMayAffect index keys edits = false then
      .ok ⟨candidate, applied, certificate.rebind _
        (assemble_transaction_stable index registry candidate edits keys applied unaffected)⟩
    else match Requirements.checkAbsent (assemble index.order candidate.dictionary) keys with
      | .error conflict => .error (.introduced candidate applied conflict)
      | .ok nextCertificate => .ok ⟨candidate, applied, nextCertificate⟩

/-- Acceptance characterizes the actual completed transaction and absence of
every watched key. A positive conservative impact is not itself a refusal. -/
theorem guardAbsenceTransaction_ok_iff (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (keys : List Key)
    (certificate : Requirements.AbsenceCertificate (assemble index.order registry.dictionary) keys)
    (edits : List (RegistryEdit Context Key Value)) :
    (∃ revision, guardAbsenceTransaction index registry keys certificate edits = .ok revision) ↔
      ∃ candidate, registry.patchTransaction edits = .ok candidate ∧
        Requirements.Absent (assemble index.order candidate.dictionary) keys := by
  constructor
  · rintro ⟨revision, _⟩
    exact ⟨revision.snapshot, revision.applied, revision.certificate.absent⟩
  · rintro ⟨candidate, applied, absent⟩
    cases outcome : guardAbsenceTransaction index registry keys certificate edits with
    | ok revision => exact ⟨revision, rfl⟩
    | error failure =>
      cases failure with
      | unknownProvider name failed => rw [applied] at failed; contradiction
      | introduced next nextApplied conflict =>
        have same : candidate = next := Except.ok.inj (applied.symm.trans nextApplied)
        subst next
        exact False.elim (conflict.refutes absent)

omit [DecidableEq Key] in
/-- Failure evidence ties an introduced method to an actual graph ancestor and
the exact selected factory, without invoking that factory. -/
theorem absenceConflict_origin (index : C4.AncestryIndex graph root)
    (candidate : ProviderRegistry Context Key Value)
    (conflict : Requirements.Presence (assemble index.order candidate.dictionary) keys) :
    ∃ name, C4.Ancestor graph name root ∧
      candidate.dictionary name conflict.key = some conflict.factory :=
  conflict.origin index.order candidate.dictionary

end LeanPoo.Functional
