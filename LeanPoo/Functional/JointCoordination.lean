import LeanPoo.Functional.JointRestaging

/-! Independent successful factories may observe equal or different prefixes.
The laws use whole snapshots and existing checked installation, not a scheduler. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- Two coordinators preparing from the same observed prefix both capture that
head. Either serialized lock order selects exactly its first complete candidate. -/
theorem restageAfter_competing {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts : List (Installation (Revision := Revision) Valid))
    (a b : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (ra rb : Revision)
    (fa : (a (installSequence current prefixAttempts)).val.id ≠ (installSequence current prefixAttempts).id)
    (fb : (b (installSequence current prefixAttempts)).val.id ≠ (installSequence current prefixAttempts).id) :
    let x : Installation (Revision := Revision) Valid := ⟨restageAfter current prefixAttempts a ra,ra⟩
    let y : Installation (Revision := Revision) Valid := ⟨restageAfter current prefixAttempts b rb,rb⟩
    installSequence (installSequence current prefixAttempts) [x,y] = x.receipt.candidate ∧
    installSequence (installSequence current prefixAttempts) [y,x] = y.receipt.candidate := by
  exact competing_orders _ _ _ rfl rfl rfl rfl fa fb
/-- A coordinator whose capture is superseded must not install its old candidate,
even if its local/joint checks and registered revisions are still true/current. -/
theorem restageAfter_superseded {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (oldPrefix newPrefix : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (staged live : Revision)
    (advanced : (installSequence current newPrefix).id ≠ (installSequence current oldPrefix).id) :
    installChecked (restageAfter current oldPrefix prepare staged).expected (installSequence current newPrefix)
      (restageAfter current oldPrefix prepare staged).candidate staged live true = installSequence current newPrefix := by
  exact checked_stale _ _ _ _ _ _ advanced
/-- Shared approval failures do not change the captured preparation source;
explicit NEW preparation after such failures observes the same whole current head. -/
theorem restageAfter_refused {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts denied : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision)
    (refused : ∀ attempt ∈ denied, (installSequence current prefixAttempts).id ≠ attempt.receipt.expected ∨
      attempt.receipt.staged ≠ attempt.live) :
    restageAfter current (prefixAttempts ++ denied) prepare revision = restageAfter current prefixAttempts prepare revision := by
  have same : installSequence current (prefixAttempts ++ denied) = installSequence current prefixAttempts := by
    rw [installSequence_append,installSequence_inert _ denied refused]
  exact congrArg (fun observed =>
    (⟨observed.id,(prepare observed).val,revision,(prepare observed).property⟩ : Approved (Revision := Revision) Valid)) same
/-- A lifecycle event reaches the existing installation boundary or records a
coordinator stopping/rejoining without publication. Earlier successful writes stay in the trace.
Stopping is NOT modelled as rolling back or accepting that coordinator's receipts. -/
inductive CoordinatorEvent (Coordinator : Type)
    (Valid : Bundle Id Endpoint Policy Head Metadata → Prop) where
  | attempt : Installation (Revision := Revision) Valid → CoordinatorEvent Coordinator Valid
  | stopped : Coordinator → CoordinatorEvent Coordinator Valid
  | rejoined : Coordinator → CoordinatorEvent Coordinator Valid
/-- Project the actual serialized installations; failed preparation and normal exit
have no owner write. Cleanup must establish this premise in the native program. -/
def coordinatorAttempts {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) : List (Installation (Revision := Revision) Valid) :=
  events.filterMap fun event => match event with
    | .attempt attempt => some attempt
    | .stopped _ => none
    | .rejoined _ => none
/-- Execute surviving installation attempts using the same checked owner protocol. -/
def installCoordinated {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) :=
  installSequence current (coordinatorAttempts events)
/-- A local stop interleaved anywhere neither rolls back earlier winners nor
cancels the remaining coordinators' later installation attempts. -/
theorem installCoordinated_stopped {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (before after : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (who : Coordinator) :
    installCoordinated current (before ++ .stopped who :: after) =
      installCoordinated current (before ++ after) := by
  simp [installCoordinated,coordinatorAttempts,List.filterMap_append]
/-- Survivors explicitly prepare from the complete current winner, including all
successful installs before a coordinator stopped. No abandoned receipt is revived. -/
theorem restageAfter_coordinator_stopped {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (before after : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (who : Coordinator)
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision) :
    restageAfter current (coordinatorAttempts (before ++ .stopped who :: after)) prepare revision =
      restageAfter current (coordinatorAttempts (before ++ after)) prepare revision := by
  simp [coordinatorAttempts,List.filterMap_append]
/-- Validity is preserved through arbitrary finite local exits and surviving
attempts, including revision refusals and competing or stale receipts. -/
theorem installCoordinated_valid {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (old : Valid current) :
    Valid (installCoordinated current events) :=
  installSequence_valid current (coordinatorAttempts events) old
/-- Rejoining itself has no publication authority: earlier installed winners
and surviving competing attempts are unaffected by the lifecycle notification. -/
theorem installCoordinated_rejoined {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (before after : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (who : Coordinator) :
    installCoordinated current (before ++ .rejoined who :: after) =
      installCoordinated current (before ++ after) := by
  simp [installCoordinated,coordinatorAttempts,List.filterMap_append]
/-- Explicit fresh preparation after recovery captures the actual prefix winner,
including publications by other coordinators while the failed operation was absent. -/
theorem restageAfter_rejoined_expected {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (who : Coordinator)
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision) :
    (restageAfter current (coordinatorAttempts (events ++ [.rejoined who])) prepare revision).expected =
      (installCoordinated current events).id := by
  simp [restageAfter,coordinatorAttempts,List.filterMap_append,installCoordinated]
/-- A recovered operation cannot revive an old receipt when the head advanced OR
its registered approval revision drifted. Restart alone does not revoke a receipt
whose captured head and registered guards are still current. -/
theorem rejoined_receipt_refused {Coordinator : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (events : List (CoordinatorEvent (Revision := Revision) Coordinator Valid)) (who : Coordinator)
    (old : Approved (Revision := Revision) Valid) (live : Revision)
    (obsolete : (installCoordinated current events).id ≠ old.expected ∨ old.staged ≠ live) :
    installCoordinated current (events ++ [.rejoined who,.attempt ⟨old,live⟩]) =
      installCoordinated current events := by
  simp only [installCoordinated,coordinatorAttempts,List.filterMap_append,List.filterMap_cons,List.filterMap_nil]
  rw [installSequence_append]
  change installChecked old.expected (installSequence current (coordinatorAttempts events)) old.candidate
    old.staged live true = _
  rcases obsolete with head | drift
  · exact checked_stale _ _ _ _ _ _ head
  · exact metadata_stale _ _ _ _ _ _ drift
end LeanPoo.Functional.JointPublication
