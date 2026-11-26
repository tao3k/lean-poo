import LeanPoo.Functional.ComponentRevision

/-! Abstract serialized installation after candidate construction and joint
approval. It models head selection, not runtime mutex or callback verification. -/
namespace LeanPoo.Functional.ComponentPublication
variable {Snapshot : Type} [DecidableEq Snapshot]
/-- One successful installation or refusal preserves the actual authoritative head. -/
structure Result (Snapshot : Type) where
  head : Snapshot
  accepted : Bool
/-- Installation rechecks the expected head after off-lock construction. Candidate
freshness and approval accuracy are caller premises, independent of this decision. -/
def install (expected current candidate : Snapshot) (approved : Bool) : Result Snapshot :=
  if current = expected ∧ approved = true then ⟨candidate,true⟩ else ⟨current,false⟩
/-- A competing successful publication cannot be overwritten by a stale candidate. -/
theorem stale (expected current candidate : Snapshot) (approved : Bool) (different : current ≠ expected) :
    install expected current candidate approved = ⟨current,false⟩ := by simp [install,different]
/-- Joint refusal retains CURRENT state, which need not be the request's old head. -/
theorem refused (expected current candidate : Snapshot) :
    install expected current candidate false = ⟨current,false⟩ := by simp [install]
/-- Accepted installation selects exactly the candidate and implies both checks. -/
theorem accepted (expected current candidate : Snapshot) (approved : Bool)
    (success : (install expected current candidate approved).accepted = true) :
    (install expected current candidate approved).head = candidate ∧ current = expected ∧ approved = true := by
  unfold install at success ⊢
  split at success
  · rename_i valid; simp [valid]
  · contradiction
/-- The first accepted fresh publication makes a sibling request staged against
its predecessor stale. No claim of automatic rebasing or merging is hidden here. -/
theorem competing (expected first second : Snapshot) (fresh : first ≠ expected) :
    install expected (install expected expected first true).head second true = ⟨first,false⟩ := by
  simp [install,fresh]
/-- Refusal permits retry on the same head after fresh policy preparation, provided
no rival has advanced it. Approval changes alone do not install an old candidate. -/
theorem retry (expected candidate : Snapshot) :
    install expected (install expected expected candidate false).head candidate true = ⟨candidate,true⟩ := by
  simp [install]
/-- Revalidate approval revision identity at the serialized installation point.
Native uses existing object revisions for all registered guards; the abstract
revision type may describe several heterogeneous services together. -/
def installChecked {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool) : Result Snapshot :=
  install expected current candidate (approved && decide (staged = live))
/-- Approval metadata drift refuses even when the publication head is unchanged
and the earlier candidate passed every approval predicate. -/
theorem metadata_stale {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool) (drift : staged ≠ live) :
    installChecked expected current candidate staged live approved = ⟨current,false⟩ := by
  simp [installChecked,drift,refused]
/-- Successful installation requires BOTH current head and the exact registered
approval revision, as well as the original candidate's true joint approval. -/
theorem checked_accepted {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool)
    (success : (installChecked expected current candidate staged live approved).accepted = true) :
    (installChecked expected current candidate staged live approved).head = candidate ∧
      current = expected ∧ approved = true ∧ staged = live := by
  have valid := accepted expected current candidate _ success
  simpa only [installChecked,Bool.and_eq_true,decide_eq_true_eq, and_assoc] using valid
/-- A fresh metadata capture can retry on an unchanged publication. A request
captured before the update remains refused; approval is never silently refreshed. -/
theorem metadata_retry {Revision : Type} [DecidableEq Revision]
    (expected candidate : Snapshot) (old live : Revision) (drift : old ≠ live) :
    installChecked expected
      (installChecked expected expected candidate old live true).head candidate live live true = ⟨candidate,true⟩ := by
  rw [metadata_stale expected expected candidate old live true drift]
  simp [installChecked,install]
/-- Any number of candidates captured at an obsolete approval revision leaves
current publication unchanged, irrespective of their candidate values or order. -/
theorem metadata_batch {Revision : Type} [DecidableEq Revision]
    (expected current : Snapshot) (staged live : Revision) (approved : Bool)
    (candidates : List Snapshot) (drift : staged ≠ live) :
    candidates.foldl (fun head candidate =>
      (installChecked expected head candidate staged live approved).head) current = current := by
  induction candidates generalizing current with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [List.foldl_cons, metadata_stale expected current candidate staged live approved drift]
    exact ih current
end LeanPoo.Functional.ComponentPublication

namespace LeanPoo.Functional.ComponentPublication

/-- One private native snapshot identity covers both payload projections. The
counter models fresh object identity even for an equal-valued publication. -/
structure Published where
  identity : Nat
  graph : Nat
  metadata : Nat
  deriving DecidableEq

/-- Families are issued by the coordinator. Advancing one explicit continuation
cannot invalidate an independently staged family merely sharing its head. -/
def advanceFamily (versions : Nat → Nat) (family : Nat) : Nat → Nat :=
  fun query => if query = family then versions query + 1 else versions query

theorem continuation_advances (versions : Nat → Nat) (family : Nat) :
    advanceFamily versions family family = versions family + 1 := by
  simp [advanceFamily]

theorem independent_family_keeps_ticket (versions : Nat → Nat)
    (first second : Nat) (different : first ≠ second) :
    advanceFamily versions second first = versions first := by
  simp [advanceFamily, different]

theorem continuation_rejects_old_result
    (expected current candidate : Published) (versions : Nat → Nat) (family : Nat)
    (approved : Bool) :
    installChecked expected current candidate (family, versions family)
      (family, advanceFamily versions family family) approved = ⟨current, false⟩ := by
  apply metadata_stale
  simp [advanceFamily]

theorem independent_family_keeps_result
    (expected current candidate : Published) (versions : Nat → Nat)
    (first second : Nat) (different : first ≠ second) (approved : Bool) :
    installChecked expected current candidate (first, versions first)
      (first, advanceFamily versions second first) approved =
    install expected current candidate approved := by
  rw [independent_family_keeps_ticket versions first second different]
  simp [installChecked]

/-- A rejected refreshed proposal never rearms the predecessor family ticket. -/
theorem failed_continuation_does_not_rearm
    (expected current rejected oldCandidate : Published)
    (versions : Nat → Nat) (family : Nat) :
    installChecked expected
      (install expected current rejected false).head oldCandidate
      (family, versions family) (family, advanceFamily versions family family) true =
      ⟨current, false⟩ := by
  rw [refused]
  exact continuation_rejects_old_result _ _ _ _ _ _

def replacement (current : Published) (graph metadata : Nat) : Published :=
  ⟨current.identity + 1, graph, metadata⟩

theorem replacement_binds_both (current : Published) (graph metadata : Nat) :
    (replacement current graph metadata).graph = graph ∧
      (replacement current graph metadata).metadata = metadata := ⟨rfl, rfl⟩

theorem no_op_still_retires_old_snapshot (old : Published) :
    replacement old old.graph old.metadata ≠ old := by
  intro same
  have impossible := congrArg Published.identity same
  simp [replacement] at impossible

/-- Source/approval entry and return checks remain independent premises. The
captured private snapshot is the sole source of both returned projections. -/
def readPublished (captured live : Published) (entryOK returnOK : Bool) :
    Option (Nat × Nat) :=
  if entryOK && returnOK && decide (captured = live) then
    some (captured.graph, captured.metadata) else none

theorem read_one_snapshot (captured live : Published) (entryOK returnOK : Bool)
    (graph metadata : Nat)
    (accepted : readPublished captured live entryOK returnOK = some (graph, metadata)) :
    captured = live ∧ graph = captured.graph ∧ metadata = captured.metadata ∧
      entryOK = true ∧ returnOK = true := by
  unfold readPublished at accepted
  split at accepted
  · rename_i checks
    have values : captured.graph = graph ∧ captured.metadata = metadata := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using accepted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checks
    exact ⟨checks.2, values.1.symm, values.2.symm, checks.1.1, checks.1.2⟩
  · contradiction

theorem stale_read_has_no_payload (captured live : Published)
    (different : captured ≠ live) (entryOK returnOK : Bool) :
    readPublished captured live entryOK returnOK = none := by
  simp [readPublished, different]

end LeanPoo.Functional.ComponentPublication
