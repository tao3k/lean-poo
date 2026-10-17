import LeanPoo.Functional.JointCoordination

/-! Multiple local recoveries preserve the actual installation trace. Lifecycle
order is arbitrary, while successful installation order remains observable. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision Coordinator : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
/-- A lifecycle-only event carries no owner write. This predicate never classifies
an attempted installation as harmless, even when its coordinator later fails. -/
def lifecycleOnly {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (event : CoordinatorEvent (Revision := Revision) Coordinator Valid) : Prop :=
  match event with
  | .attempt _ => False
  | .stopped _ => True
  | .rejoined _ => True
/-- Arbitrarily interleaved stops/rejoins of multiple names have no installation
projection. Actual writes are retained separately, including writes before failure. -/
theorem coordinatorAttempts_lifecycle {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid))
    (only : ∀ event ∈ events, lifecycleOnly event) : coordinatorAttempts events = [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have first := only event (by simp)
    have tail := ih (fun next member => only next (by simp [member]))
    cases event with
    | attempt attempt => exact False.elim first
    | stopped who => simpa [coordinatorAttempts] using tail
    | rejoined who => simpa [coordinatorAttempts] using tail
variable [DecidableEq Id] [DecidableEq Revision]
/-- A finite recovery wave can be inserted anywhere without rolling back a prefix
winner or changing the surviving attempts' order. Names and ordering are unrestricted. -/
theorem installCoordinated_recoveryWave {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (before wave after : List (CoordinatorEvent (Revision := Revision) Coordinator Valid))
    (only : ∀ event ∈ wave, lifecycleOnly event) :
    installCoordinated current (before ++ wave ++ after) = installCoordinated current (before ++ after) := by
  simp only [installCoordinated,coordinatorAttempts,List.filterMap_append]
  change installSequence current (coordinatorAttempts before ++ coordinatorAttempts wave ++ coordinatorAttempts after) = _
  rw [coordinatorAttempts_lifecycle wave only]
  simp only [List.append_nil]
  rfl
omit [DecidableEq Id] [DecidableEq Revision] in
/-- Embedding actual attempts as lifecycle-trace installation events is lossless. -/
theorem coordinatorAttempts_attempts {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (attempts : List (Installation (Revision := Revision) Valid)) :
    coordinatorAttempts (Coordinator := Coordinator) (attempts.map .attempt) = attempts := by
  induction attempts with
  | nil => rfl
  | cons attempt rest ih => simpa [coordinatorAttempts] using congrArg (List.cons attempt) ih
omit [DecidableEq Id] [DecidableEq Revision] in
/-- Concatenating lifecycle traces retains the exact installation order. -/
theorem coordinatorAttempts_append {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (before after : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) :
    coordinatorAttempts (before ++ after) = coordinatorAttempts before ++ coordinatorAttempts after := by
  simp only [coordinatorAttempts,List.filterMap_append]
/-- Multiple recovering coordinators may replay different historical generations.
Each head/guard-stale attempt refuses against the actual prefix winner, regardless
of intervening no-write lifecycle events or receipt ordering. -/
theorem recoveryWave_refused {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events wave : List (CoordinatorEvent (Revision := Revision) Coordinator Valid))
    (historical : List (Installation (Revision := Revision) Valid))
    (only : ∀ event ∈ wave, lifecycleOnly event)
    (obsolete : ∀ attempt ∈ historical,
      (installCoordinated current events).id ≠ attempt.receipt.expected ∨ attempt.receipt.staged ≠ attempt.live) :
    installCoordinated current (events ++ wave ++ historical.map .attempt) = installCoordinated current events := by
  rw [installCoordinated_recoveryWave current events wave _ only]
  change installSequence current (coordinatorAttempts (events ++ historical.map .attempt)) = _
  rw [coordinatorAttempts_append,coordinatorAttempts_attempts,installSequence_append]
  exact installSequence_inert _ historical obsolete
/-- Fresh valid factories after any such recovery/replay wave see the same whole
winner. No historical receipt is silently rebound to that winner by recovery. -/
theorem restageAfter_recoveryWave {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events wave : List (CoordinatorEvent (Revision := Revision) Coordinator Valid))
    (historical : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision)
    (only : ∀ event ∈ wave, lifecycleOnly event)
    (obsolete : ∀ attempt ∈ historical,
      (installCoordinated current events).id ≠ attempt.receipt.expected ∨ attempt.receipt.staged ≠ attempt.live) :
    restageAfter current (coordinatorAttempts (events ++ wave ++ historical.map .attempt)) prepare revision =
      restageAfter current (coordinatorAttempts events) prepare revision := by
  have same := recoveryWave_refused current events wave historical only obsolete
  exact congrArg (fun observed =>
    (⟨observed.id,(prepare observed).val,revision,(prepare observed).property⟩ : Approved (Revision := Revision) Valid)) same
end LeanPoo.Functional.JointPublication
