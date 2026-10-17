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
/-- Recovery preparation may fail. Only an actual successful valid factory result
can mint a receipt, capturing the explicitly supplied current whole snapshot. -/
def prepareRejoining {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → Except Error {candidate // Valid candidate})
    (revision : Revision) : Except Error (Approved (Revision := Revision) Valid) :=
  (prepare current).map fun candidate => ⟨current.id,candidate.val,revision,candidate.property⟩
omit [DecidableEq Id] [DecidableEq Revision] in
/-- A failed factory preserves its exact error and never returns an approval. -/
theorem prepareRejoining_failed {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → Except Error {candidate // Valid candidate})
    (revision : Revision) (failure : Error) (failed : prepare current = .error failure) :
    prepareRejoining current prepare revision = .error failure := by
  simp [prepareRejoining,failed,Except.map]
omit [DecidableEq Id] [DecidableEq Revision] in
/-- Success retains the checked candidate and its proof, capturing THIS snapshot;
a retry does not rebind a historical receipt or manufacture a validity witness. -/
theorem prepareRejoining_success {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → Except Error {candidate // Valid candidate})
    (revision : Revision) (candidate : {candidate // Valid candidate}) (ready : prepare current = .ok candidate) :
    prepareRejoining current prepare revision = .ok ⟨current.id,candidate.val,revision,candidate.property⟩ := by
  simp [prepareRejoining,ready,Except.map]
/-- Rejoining observes the prepared receipt's original head and registered guard
revision. It grants no reservation: installation must check them again. -/
def checkRejoining {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (live : Revision) : Option (Approved (Revision := Revision) Valid) :=
  if current.id = receipt.expected ∧ receipt.staged = live then some receipt else none
/-- A competing publication or registered metadata change rejects successful
preparation without invoking any service continuation or minting a new receipt. -/
theorem checkRejoining_stale {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (live : Revision)
    (stale : current.id ≠ receipt.expected ∨ receipt.staged ≠ live) :
    checkRejoining current receipt live = none := by
  rcases stale with head | guard
  · simp [checkRejoining, head]
  · simp [checkRejoining, guard]
/-- Compose the service continuation only after the successful observation.
This pure stage grants no installation authority and never retries implicitly. -/
def resumeRejoining {Result : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (live : Revision)
    (proceed : Approved (Revision := Revision) Valid → Result) : Option Result :=
  (checkRejoining current receipt live).map proceed
/-- Stale successful preparation cannot enter a continuation, for ANY pure
continuation and result type. The owner's state is not an output of this gate. -/
theorem resumeRejoining_stale {Result : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (live : Revision)
    (proceed : Approved (Revision := Revision) Valid → Result)
    (stale : current.id ≠ receipt.expected ∨ receipt.staged ≠ live) :
    resumeRejoining current receipt live proceed = none := by
  simp [resumeRejoining, checkRejoining_stale current receipt live stale]
/-- A fresh observation preserves the exact receipt; no historical rebase occurs. -/
theorem checkRejoining_fresh {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (live : Revision)
    (head : current.id = receipt.expected) (guard : receipt.staged = live) :
    checkRejoining current receipt live = some receipt := by
  simp [checkRejoining, head, guard]
/-- Even after successful rejoining observation, a later competing installation
or guard change still refuses at installation and retains the actual winner. -/
theorem checkRejoining_install_stale {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current later : Bundle Id Endpoint Policy Head Metadata)
    (receipt : Approved (Revision := Revision) Valid) (observed live : Revision)
    (_checked : checkRejoining current receipt observed = some receipt)
    (stale : later.id ≠ receipt.expected ∨ receipt.staged ≠ live) :
    installSequence later [⟨receipt,live⟩] = later := by
  apply installSequence_inert
  intro attempt member
  simp only [List.mem_singleton] at member
  subst attempt
  exact stale
/-- Project only successfully prepared installation requests. Original Except
results retain their errors; projection is not exception swallowing or rollback. -/
def rejoiningAttempts {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (results : List (Except Error (Installation (Revision := Revision) Valid))) : List (Installation (Revision := Revision) Valid) :=
  results.filterMap fun result => match result with
    | .error _ => none
    | .ok attempt => some attempt
/-- Serialized installation of completed requests reuses all existing owner checks. -/
def installRejoining {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (results : List (Except Error (Installation (Revision := Revision) Valid))) :=
  installSequence current (rejoiningAttempts results)
/-- A preparation failure interleaved anywhere neither rolls back an installed
prefix nor cancels other coordinators' remaining successful requests. -/
theorem installRejoining_failed {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (before after : List (Except Error (Installation (Revision := Revision) Valid))) (failure : Error) :
    installRejoining current (before ++ .error failure :: after) = installRejoining current (before ++ after) := by
  simp [installRejoining,rejoiningAttempts,List.filterMap_append]
/-- Validity survives arbitrarily many failed preparations and successful checked
requests. This is a finite trace property, not guaranteed eventual recovery. -/
theorem installRejoining_valid {Error : Type} {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata)
    (results : List (Except Error (Installation (Revision := Revision) Valid))) (old : Valid current) :
    Valid (installRejoining current results) := installSequence_valid _ _ old
end LeanPoo.Functional.JointPublication
