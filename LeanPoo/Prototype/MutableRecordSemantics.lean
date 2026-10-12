import LeanPoo.Prototype.MutableRecord

/-! Operational correspondence for the paper's identity/slot/mix!/failure
operations. The executable pure, mutable snapshot and linear reference APIs
use the interpreter proved here. No host runtime or compiler laws are assumed. -/
namespace LeanPoo.Prototype.MutableRecord

variable {State Source Target : Type}

inductive Executes (put : State → String → SlotLayer → State) :
    Specification → State → State → Except String Unit → Prop where
  | identity : Executes put .identity state state (.ok ())
  | slot : Executes put (.slot key layer) state (put state key layer) (.ok ())
  | error : Executes put (.error message) state state (.error message)
  | compose_success : Executes put parent state inherited (.ok ()) →
      Executes put child inherited final status →
      Executes put (.compose child parent) state final status
  | compose_failure : Executes put parent state inherited (.error message) →
      Executes put (.compose child parent) state inherited (.error message)

theorem interpret_sound (put : State → String → SlotLayer → State)
    (specification : Specification) (state : State) :
    Executes put specification state (specification.interpret put state).1
      (specification.interpret put state).2 := by
  induction specification generalizing state with
  | identity => exact .identity
  | slot key layer => exact .slot
  | error message => exact .error
  | compose child parent childIH parentIH =>
    cases result : parent.interpret put state with
    | mk inherited status =>
      have parentRun := parentIH state
      rw [result] at parentRun
      cases status with
      | error message => simpa [Specification.interpret, result] using
          Executes.compose_failure (child := child) parentRun
      | ok value =>
        cases value
        simpa [Specification.interpret, result] using
          Executes.compose_success parentRun (childIH inherited)

theorem interpret_complete (run : Executes put specification state final status) :
    specification.interpret put state = (final, status) := by
  induction run with
  | identity => rfl
  | slot => rfl
  | error => rfl
  | compose_success _ _ parentIH childIH =>
    simp only [Specification.interpret, parentIH]
    exact childIH
  | compose_failure _ parentIH => simp [Specification.interpret, parentIH]

theorem executes_iff : Executes put specification state final status ↔
    specification.interpret put state = (final, status) := by
  constructor
  · exact interpret_complete
  · intro result
    have run := interpret_sound put specification state
    simpa [result] using run

theorem executes_unique (first : Executes put specification state final status)
    (second : Executes put specification state final' status') :
    final = final' ∧ status = status' := by
  have equal := (interpret_complete first).symm.trans (interpret_complete second)
  exact Prod.mk.inj equal

/-- Any representation whose slot write commutes with projection preserves
the complete outcome, including the partial state and first failure. -/
theorem interpret_projection (project : Source → Target)
    (sourceWrite : Source → String → SlotLayer → Source)
    (targetWrite : Target → String → SlotLayer → Target)
    (commutes : ∀ state key layer,
      project (sourceWrite state key layer) = targetWrite (project state) key layer)
    (specification : Specification) (state : Source) :
    (project (specification.interpret sourceWrite state).1,
      (specification.interpret sourceWrite state).2) =
      specification.interpret targetWrite (project state) := by
  induction specification generalizing state with
  | identity => rfl
  | slot key layer => exact congrArg (fun value => (value, Except.ok ())) (commutes state key layer)
  | error message => rfl
  | compose child parent childIH parentIH =>
    cases result : parent.interpret sourceWrite state with
    | mk inherited status =>
      have related := parentIH state
      rw [result] at related
      cases status with
      | error message => simp [Specification.interpret, result, ← related]
      | ok value => simpa [Specification.interpret, result, ← related] using childIH inherited

theorem snapshot_projection (specification : Specification) (snapshot : Snapshot) :
    ((specification.snapshotTransition snapshot).1.storage,
      (specification.snapshotTransition snapshot).2) =
      specification.transition snapshot.storage :=
  interpret_projection Snapshot.storage Snapshot.write write (fun _ _ _ => rfl) _ _

theorem snapshot_observation (specification : Specification) (snapshot : Snapshot)
    (depth : Nat) (key : String) :
    readPure (specification.snapshotTransition snapshot).1.storage depth key =
      readPure (specification.transition snapshot.storage).1 depth key := by
  have same := congrArg Prod.fst (snapshot_projection specification snapshot)
  dsimp only at same
  rw [same]

theorem linear_success (specification : Specification) (storage final : Storage)
    (success : specification.transition storage = (final, .ok ())) :
    LinearState.stepValue (some storage) specification.transition = (none, .ok final) := by
  simp [LinearState.stepValue, success]

theorem linear_failure (specification : Specification) (storage final : Storage)
    (message : String) (failure : specification.transition storage = (final, .error message)) :
    LinearState.stepValue (some storage) specification.transition =
      (some final, .error message) := by
  simp [LinearState.stepValue, failure]

/-- Every slot observation after a failed linear operation is the same as
the pure protocol's partial state, for every key and observation depth. -/
theorem linear_failure_observation (specification : Specification) (storage final : Storage)
    (message : String) (failure : specification.transition storage = (final, .error message))
    (depth : Nat) (key : String) :
    (LinearState.stepValue (some storage) specification.transition).1.map
      (fun retained => readPure retained depth key) = some (readPure final depth key) := by
  rw [linear_failure specification storage final message failure]
  rfl

theorem parent_failure_skips_child (child parent : Specification) (state final : Storage)
    (message : String) (failure : parent.transition state = (final, .error message)) :
    (Specification.compose child parent).transition state = (final, .error message) := by
  simpa only [Specification.transition] using
    interpret_complete (Executes.compose_failure (child := child)
      ((executes_iff).mpr failure))

theorem snapshot_generation_mono (specification : Specification) (snapshot : Snapshot) :
    snapshot.generation ≤ (specification.snapshotTransition snapshot).1.generation := by
  change snapshot.generation ≤ (specification.interpret Snapshot.write snapshot).1.generation
  induction specification generalizing snapshot with
  | identity => exact Nat.le_refl _
  | error message => exact Nat.le_refl _
  | slot key layer => exact Nat.le_succ _
  | compose child parent childIH parentIH =>
    cases result : parent.interpret Snapshot.write snapshot with
    | mk inherited status =>
      have prior := parentIH snapshot
      rw [result] at prior
      cases status with
      | error message => simpa only [Specification.interpret, result] using prior
      | ok value =>
        simpa only [Specification.interpret, result] using Nat.le_trans prior (childIH inherited)

theorem snapshot_unchanged_of_generation_eq (specification : Specification) (snapshot : Snapshot)
    (same : (specification.snapshotTransition snapshot).1.generation = snapshot.generation) :
    (specification.snapshotTransition snapshot).1 = snapshot := by
  change (specification.interpret Snapshot.write snapshot).1.generation = snapshot.generation at same
  change (specification.interpret Snapshot.write snapshot).1 = snapshot
  induction specification generalizing snapshot with
  | identity => rfl
  | error message => rfl
  | slot key layer => simp [Specification.interpret, Snapshot.write] at same
  | compose child parent childIH parentIH =>
    cases result : parent.interpret Snapshot.write snapshot with
    | mk inherited status =>
      have prior := snapshot_generation_mono parent snapshot
      change snapshot.generation ≤ (parent.interpret Snapshot.write snapshot).1.generation at prior
      rw [result] at prior
      cases status with
      | error message =>
        simp only [Specification.interpret, result] at same ⊢
        have unchanged := parentIH snapshot (by simpa only [result] using same)
        simpa only [result] using unchanged
      | ok value =>
        simp only [Specification.interpret, result] at same ⊢
        have later := snapshot_generation_mono child inherited
        change inherited.generation ≤ (child.interpret Snapshot.write inherited).1.generation at later
        dsimp only at prior same
        have equal : inherited.generation = snapshot.generation := by omega
        have unchanged := parentIH snapshot (by simpa only [result] using equal)
        have nextUnchanged := childIH inherited (by omega)
        rw [nextUnchanged]
        simpa only [result] using unchanged

end LeanPoo.Prototype.MutableRecord
