import LeanPoo.Functional.StagedPublication
import LeanPoo.Object.Migration

/-! Explicit typed data transfers into a differently typed graph, followed by
existing construction/family admission and atomic version switching. Future work. -/
namespace LeanPoo.Functional.CarrierMigration
open GeneralizedGraph
variable {SourceKey TargetKey : Type} {SourceValue : SourceKey → Type} {TargetValue : TargetKey → Type}
variable [DecidableEq TargetKey]

abbrev Transfer := Object.FieldTransfer SourceKey SourceValue TargetKey TargetValue

inductive Failure (SourceKey : Type) (TargetKey : Type) where
  | shape (error : Object.MigrationError SourceKey TargetKey)
  | source (key : SourceKey) (error : ComputationError SourceKey)
  deriving Repr

/-- Only successful source data is exposed to the existing field converter.
An actual failed source slot refuses before defaulting or conversion. -/
def read (source : State SourceKey SourceValue) (transfer : Transfer (SourceKey := SourceKey) (TargetKey := TargetKey)
    (SourceValue := SourceValue) (TargetValue := TargetValue)) :
    Except (Failure SourceKey TargetKey) (Option (TargetValue transfer.target)) :=
  match source transfer.source with
  | some (.error error) => .error (.source transfer.source error)
  | _ => (transfer.evaluate (fun key => (source key).bind Except.toOption)).mapError Failure.shape

omit [DecidableEq TargetKey] in
theorem read_failed (source : State SourceKey SourceValue)
    (transfer : Transfer (SourceValue := SourceValue) (TargetValue := TargetValue))
    (error : ComputationError SourceKey) (failed : source transfer.source = some (.error error)) :
    read source transfer = .error (.source transfer.source error) := by simp [read, failed]

/-- Validate the entire target shape before evaluating any converter. The target
support must declare a noncomputed slot; omitted fields keep target defaults. -/
def validate (target : Declaration TargetKey TargetValue) (seen : List TargetKey) :
    List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)) →
    Except (Failure SourceKey TargetKey) Unit
  | [] => .ok ()
  | transfer :: rest =>
    if transfer.target ∈ seen then .error (.shape (.duplicateTarget transfer.target))
    else if transfer.target ∉ target.keys then .error (.shape (.unknownTarget transfer.target))
    else if (target.code transfer.target).isSome then .error (.shape (.nonDataTarget transfer.target))
    else validate target (transfer.target :: seen) rest

def apply (source : State SourceKey SourceValue) (base : State TargetKey TargetValue) :
    List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)) →
    Except (Failure SourceKey TargetKey) (State TargetKey TargetValue)
  | [] => .ok base
  | transfer :: rest => match read source transfer with
    | .error error => .error error
    | .ok none => apply source base rest
    | .ok (some value) => apply source (setSlot base transfer.target (some (.ok value))) rest

/-- Complete conversion precedes graph scheduling and construction; a successful
transfer installs data, never a copied source computation or source cache. -/
def prepare (source : State SourceKey SourceValue) (target : Declaration TargetKey TargetValue)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue))) :
    Except (Failure SourceKey TargetKey) (Declaration TargetKey TargetValue) :=
  match validate target [] transfers with
  | .error error => .error error
  | .ok () => (apply source target.base transfers).map fun base => {target with base}

theorem prepare_shape_first (source : State SourceKey SourceValue) (target : Declaration TargetKey TargetValue)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (error : Failure SourceKey TargetKey) (invalid : validate target [] transfers = .error error) :
    prepare source target transfers = .error error := by simp [prepare, invalid]

/-- No unlisted target key is modified by a successful conversion batch. -/
theorem apply_frame (source : State SourceKey SourceValue) (base : State TargetKey TargetValue)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (next : State TargetKey TargetValue) (key : TargetKey)
    (outside : ∀ transfer ∈ transfers, transfer.target ≠ key) (done : apply source base transfers = .ok next) :
    next key = base key := by
  induction transfers generalizing base with
  | nil => cases done; rfl
  | cons transfer rest ih =>
    unfold apply at done
    split at done
    · contradiction
    · exact ih base (fun item member => outside item (by simp [member])) done
    · rename_i value found
      have same := ih (setSlot base transfer.target (some (.ok value)))
        (fun item member => outside item (by simp [member])) done
      simpa [setSlot, outside transfer (by simp)] using same

/-- A data slot in any materialized target is its declared base value. -/
theorem data_value (spec : Declaration TargetKey TargetValue) (cache : ConstructionCache.Cache spec)
    (key : TargetKey) (data : spec.code key = none) : cache.closed.raw key = spec.base key := by
  have fixed := cache.closed.fixed
  rw [spec.step_eq] at fixed
  have cell := congrFun fixed key
  unfold Declaration.resolve at cell
  split at cell <;> simpa [data] using cell.symm

variable {OtherValue : SourceKey → Type}

/-- Every successful batch exposes its exact conversion outcome and retains the
entire target declaration code/support. Only the base data can change. -/
theorem prepare_origin (source : State SourceKey SourceValue) (target : Declaration TargetKey TargetValue)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (next : Declaration TargetKey TargetValue) (done : prepare source target transfers = .ok next) :
    next.keys = target.keys ∧ next.code = target.code ∧ apply source target.base transfers = .ok next.base := by
  unfold prepare at done
  split at done
  · contradiction
  · rename_i valid
    cases converted : apply source target.base transfers with
    | error error => simp [converted, Except.map] at done
    | ok base =>
      simp [converted, Except.map] at done
      cases done
      exact ⟨rfl,rfl,rfl⟩

/-- The written cell comes from the actual converter. Unrelated subsequent
transfers cannot overwrite it. This includes renamed and type-changing cells. -/
theorem apply_head (source : State SourceKey SourceValue) (base : State TargetKey TargetValue)
    (transfer : Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)) (rest : List (Transfer
      (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (value : TargetValue transfer.target) (next : State TargetKey TargetValue)
    (readOk : read source transfer = .ok (some value))
    (unique : ∀ other ∈ rest, other.target ≠ transfer.target)
    (done : apply source base (transfer :: rest) = .ok next) :
    next transfer.target = some (.ok value) := by
  simp only [apply, readOk] at done
  have frame := apply_frame source (setSlot base transfer.target (some (.ok value))) rest next transfer.target unique done
  simpa [setSlot] using frame

/-- Convert stored payloads through explicit exact representation bridges while
preserving true absence and exact source failures. This does not reuse a cache. -/
def represent (bridge : (key : SourceKey) → Prototype.DictionaryBridge (SourceValue key) (OtherValue key))
    (source : State SourceKey SourceValue) : State SourceKey OtherValue :=
  fun key => (source key).map (fun outcome => outcome.map (bridge key).toFields)

theorem represent_roundtrip
    (bridge : (key : SourceKey) → Prototype.DictionaryBridge (SourceValue key) (OtherValue key))
    (source : State SourceKey SourceValue) :
    represent (fun key => (bridge key).inverse) (represent bridge source) = source := by
  funext key
  cases found : source key with
  | none => simp [represent, found]
  | some outcome => cases outcome <;> simp [represent, found, Except.map, Prototype.DictionaryBridge.inverse, (bridge key).from_to]

/-- Data conversion feeds the existing target constructor and family admission.
No source method, cache or candidate approval is coerced into the new carrier. -/
def rebuild {G Policy Cooked : Type} {Args Method Result : G → Type}
    [BEq TargetKey] [LawfulBEq TargetKey] [Hashable TargetKey]
    [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
    (model : StagedPublication.Model TargetKey TargetValue G Policy Cooked Args Method Result)
    {Approved : (current : GeneralizedMOP.Request TargetKey TargetValue Policy) → StagedPublication.Candidate model current → Type}
    {BuildIssue AdmissionIssue : Type}
    (source : State SourceKey SourceValue) (target : Declaration TargetKey TargetValue) (policy : Policy)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (builder : (spec : Declaration TargetKey TargetValue) → ConstructionCache.Builder spec BuildIssue)
    (admit : (current : GeneralizedMOP.Request TargetKey TargetValue Policy) → (candidate : StagedPublication.Candidate model current) →
      Except AdmissionIssue (Approved current candidate)) :
    Except (Sum (Failure SourceKey TargetKey)
      (StagedPublication.Failure (BuildError := BuildIssue) (AdmissionError := AdmissionIssue) model))
      (StagedPublication.Snapshot model Approved) :=
  match prepare source target transfers with
  | .error error => .error (.inl error)
  | .ok graph => match StagedPublication.start model ⟨graph,policy⟩ (builder graph) admit with
    | .error error => .error (.inr error)
    | .ok prepared => .ok (prepared.snapshot model)


theorem rebuild_origin {G Policy Cooked : Type} {Args Method Result : G → Type}
    [BEq TargetKey] [LawfulBEq TargetKey] [Hashable TargetKey]
    [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
    (model : StagedPublication.Model TargetKey TargetValue G Policy Cooked Args Method Result)
    {Approved : (current : GeneralizedMOP.Request TargetKey TargetValue Policy) → StagedPublication.Candidate model current → Type}
    {BuildIssue AdmissionIssue : Type}
    (source : State SourceKey SourceValue) (target : Declaration TargetKey TargetValue) (policy : Policy)
    (transfers : List (Transfer (SourceValue := SourceValue) (TargetValue := TargetValue)))
    (builder : (spec : Declaration TargetKey TargetValue) → ConstructionCache.Builder spec BuildIssue)
    (admit : (current : GeneralizedMOP.Request TargetKey TargetValue Policy) → (candidate : StagedPublication.Candidate model current) →
      Except AdmissionIssue (Approved current candidate))
    (next : StagedPublication.Snapshot model Approved)
    (accepted : rebuild model source target policy transfers builder admit = .ok next) :
    ∃ actual, prepare source target transfers = .ok actual ∧ next.request = ⟨actual,policy⟩ := by
  unfold rebuild at accepted
  split at accepted
  · contradiction
  · rename_i actual converted
    split at accepted
    · contradiction
    · cases accepted
      exact ⟨actual,converted,rfl⟩

universe u v w
variable {Old : Type u} {New : Type v} {Issue : Type w}

/-- Source and target may have different key/value, policy, cooked, generic,
argument and result carriers. Refusal returns the exact old approved snapshot. -/
def publish (old : Old) (prepareTarget : Old → Except Issue New) : Except Issue New × Sum Old New :=
  let outcome := prepareTarget old
  (outcome,match outcome with | .error _ => .inl old | .ok next => .inr next)

theorem publish_refused (old : Old) (prepareTarget : Old → Except Issue New) (error : Issue)
    (refused : prepareTarget old = .error error) : (publish old prepareTarget).2 = .inl old := by
  simp [publish, refused]

theorem publish_accepted (old : Old) (prepareTarget : Old → Except Issue New) (next : New)
    (accepted : prepareTarget old = .ok next) : (publish old prepareTarget).2 = .inr next := by
  simp [publish, accepted]

end LeanPoo.Functional.CarrierMigration
