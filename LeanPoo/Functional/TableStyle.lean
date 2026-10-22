import LeanPoo.Functional.TableRepresentation
import LeanPoo.Prototype.LinearState

/-! Generated collection styles over one persistent backend. The model covers
atomic staged updates and dynamic ownership, not static linear types or rollback
of arbitrary callback effects. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Pure values, stable mutable identities, and consume-old/return-new references. -/
inductive TableStyle where
  | pure | mutable | linear
  deriving DecidableEq, Repr

/-- Ownership refusal is separate from an unchanged original backend cause. -/
inductive StyleFailure (E : Type) where
  | consumed | stale | callback (cause : E)
  deriving DecidableEq, Repr

/-- One atomic table transformation; a failure exposes no intermediate writes. -/
def styleStep (style : TableStyle) (state : Option A) (update : A → Except E A) :
    Option A × Except (StyleFailure E) A :=
  match state with
  | none => (none, .error .consumed)
  | some before =>
    match update before with
    | .error cause => (state, .error (.callback cause))
    | .ok after =>
      (match style with
       | .pure => state
       | .mutable => some after
       | .linear => none, .ok after)

/-- Pure snapshots are duplicable; converting any owned reference retires aliases.
The target receives the exact admitted payload in a separately prepared successor. -/
def styleConvert (source target : TableStyle) (state : Option A) :
    Option A × Except (StyleFailure E) (TableStyle × A) :=
  match state with
  | none => (none, .error .consumed)
  | some value => (if source = .pure then state else none, .ok (target, value))

/-- The successful result is independent of style, including exact failure causes. -/
theorem styleStep_result (left right : TableStyle) (state : Option A) (update : A → Except E A) :
    (styleStep left state update).2 = (styleStep right state update).2 := by
  cases state with
  | none => rfl
  | some before => cases h : update before <;> simp [styleStep, h]

/-- Callback refusal preserves the original reference and cause in every style. -/
theorem styleStep_failure (style : TableStyle) (before : A) (update : A → Except E A)
    (cause : E) (h : update before = .error cause) :
    styleStep style (some before) update = (some before, .error (.callback cause)) := by
  simp [styleStep, h]

/-- No callback is evaluated after ownership has been consumed. -/
theorem styleStep_consumed (style : TableStyle) (update : A → Except E A) :
    styleStep style none update = (none, .error .consumed) := rfl

/-- Pure update returns the new value while retaining the entire prior snapshot. -/
theorem styleStep_pure (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .pure (some before) update = (some before, .ok after) := by simp [styleStep, h]

/-- Mutable update changes the payload of the one retained identity. -/
theorem styleStep_mutable (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .mutable (some before) update = (some after, .ok after) := by simp [styleStep, h]

/-- Linear success retires every old alias and returns the successor payload. -/
theorem styleStep_linear (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .linear (some before) update = (none, .ok after) := by simp [styleStep, h]

/-- All nine conversions preserve the same observed payload and exact target style. -/
theorem styleConvert_observation (source target : TableStyle) (value : A) :
    (styleConvert (E := E) source target (some value)).2 = .ok (target, value) := rfl

/-- Owned conversion consumes the source even when the target has the same style. -/
theorem styleConvert_owned (source target : TableStyle) (value : A) (owned : source ≠ .pure) :
    (styleConvert (E := E) source target (some value)).1 = none := by simp [styleConvert, owned]

/-- Pure conversion does not retire the original duplicable snapshot. -/
theorem styleConvert_pure (target : TableStyle) (value : A) :
    (styleConvert (E := E) .pure target (some value)).1 = some value := by simp [styleConvert]

/-- Conversion cannot revive a consumed owner. -/
theorem styleConvert_consumed (source target : TableStyle) :
    styleConvert (A := A) (E := E) source target none = (none, .error .consumed) := rfl

/-- The atomic linear specialization reuses the existing partial-state reference
semantics by retaining before on error. It does not change that lower-level API. -/
theorem styleStep_linear_existing (before : A) (update : A → Except String A) :
    styleStep .linear (some before) update =
      Prod.map id (fun result => result.mapError StyleFailure.callback)
      (LeanPoo.Prototype.LinearState.stepValue (some before) (fun value =>
        match update value with
        | .error cause => (value, .error cause)
        | .ok after => (after, .ok ()))) := by
  cases h : update before <;> simp [styleStep, LeanPoo.Prototype.LinearState.stepValue, Except.mapError, h]

/-- A private immutable generation distinguishes ABA changes even at equal values. -/
structure TableGeneration (A : Type) where
  version : Nat
  value : Option A
  deriving DecidableEq, Repr

/-- Installation checks a captured generation before applying any staged result. -/
def installStyle (style : TableStyle) (current : TableGeneration A) (expected : Nat)
    (after : A) : TableGeneration A × Except (StyleFailure E) A :=
  if current.version ≠ expected ∨ current.value.isNone then
    (current, .error .stale)
  else
    (⟨current.version + 1, if style = .linear then none else some after⟩, .ok after)

/-- A losing callback cannot overwrite or resurrect a newer generation. -/
theorem installStyle_stale (style : TableStyle) (current : TableGeneration A) (expected : Nat)
    (after : A) (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected after = (current, .error .stale) := by
  simp [installStyle, stale]

/-- A retired head refuses installation even if its version matches. -/
theorem installStyle_retired (style : TableStyle) (version : Nat) (after : A) :
    installStyle (E := E) style ⟨version, none⟩ version after =
      (⟨version, none⟩, .error .stale) := by simp [installStyle]

/-- Returning to an equal table value still invalidates an earlier staged update. -/
theorem installStyle_aba (style : TableStyle) (version : Nat) (before after : A) :
    installStyle (E := E) style ⟨version + 2, some before⟩ version after =
      (⟨version + 2, some before⟩, .error .stale) := by simp [installStyle]

/-- The first installed owned successor invalidates every request with the same
captured generation, regardless of its payload or chosen reference style. -/
theorem installStyle_single_winner (style other : TableStyle) (version : Nat)
    (before first second : A) :
    let winner := (installStyle (E := E) style ⟨version, some before⟩ version first).1
    installStyle (E := E) other winner version second = (winner, .error .stale) := by
  dsimp
  apply installStyle_stale
  simp [installStyle]

/-- Exact whole-batch carrier execution supplies the same success to every style. -/
theorem styleStep_table_success [DecidableEq K] [DecidableEq V]
    (ops : TableCarrier K V A) (style : TableStyle) (edits : List (Change K V))
    (before after : A) (h : ops.apply edits before = .ok after) :
    (styleStep style (some before) (ops.apply edits)).2 = .ok after := by simp [styleStep, h]

/-- A late delta conflict keeps the whole old snapshot, not a partially edited root. -/
theorem styleStep_table_conflict [DecidableEq K] [DecidableEq V]
    (ops : TableCarrier K V A) (style : TableStyle) (edits : List (Change K V))
    (before : A) (key : K) (h : ops.apply edits before = .error key) :
    styleStep style (some before) (ops.apply edits) = (some before, .error (.callback key)) :=
  styleStep_failure style before (ops.apply edits) key h

end LeanPoo.Functional.OrderedDictionary
