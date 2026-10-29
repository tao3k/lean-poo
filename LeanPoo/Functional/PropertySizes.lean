import LeanPoo.Functional.PropertyGenerators

/-! Size control on a known generator. Pure size laws do not justify fusing
host callbacks: callbacks may revise owners or throw. Guarded execution below
keeps those boundaries. Value can denote a whole retained shrinking tree.
No host PRNG quality, callback termination or wall-clock claim is made. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Replace the size without splitting or advancing the delegated seed. -/
def resizeDraw (draw : Seed → Nat → Value × Seed) (size : Nat)
    (seed : Seed) (_outer : Nat) : Value × Seed := draw seed size

/-- Transform the size while delegating the identical seed and result. -/
def scaleDraw (draw : Seed → Nat → Value × Seed) (scale : Nat → Nat)
    (seed : Seed) (size : Nat) : Value × Seed := draw seed (scale size)

/-- The innermost explicit resize determines the delegated size. -/
theorem resizeDraw_nested (draw : Seed → Nat → Value × Seed) (inner outer : Nat) :
    resizeDraw (resizeDraw draw inner) outer = resizeDraw draw inner := rfl

/-- Identity scaling preserves both the value and returned seed. -/
theorem scaleDraw_identity (draw : Seed → Nat → Value × Seed) :
    scaleDraw draw id = draw := rfl

/-- Pure total scales compose in outer-to-inner evaluation order. -/
theorem scaleDraw_composition (draw : Seed → Nat → Value × Seed) (inner outer : Nat → Nat) :
    scaleDraw (scaleDraw draw inner) outer = scaleDraw draw (inner ∘ outer) := rfl

/-- Scaling forwards exactly the selected draw, including its retained tree. -/
theorem scaleDraw_delegates (draw : Seed → Nat → Value × Seed)
    (scale : Nat → Nat) (seed : Seed) (size : Nat) :
    scaleDraw draw scale seed size = draw seed (scale size) := rfl

/-- Check the owner's authority before/after scaling and before/after drawing.
The state includes source revisions and random state; errors keep their cause. -/
def guardedSize (live : State → Bool)
    (scale : Nat → State → Except Cause (Nat × State))
    (draw : Nat → State → Except Cause (Value × State))
    (size : Nat) (state : State) : Except (Option Cause) (Value × State) :=
  match guardedGeneration live (scale size) state with
  | .error cause => .error cause
  | .ok result => guardedGeneration live (draw result.1) result.2

/-- An obsolete input suppresses both scaling and delegated drawing. -/
theorem guardedSize_stale (live : State → Bool)
    (scale : Nat → State → Except Cause (Nat × State))
    (draw : Nat → State → Except Cause (Value × State))
    (size : Nat) (state : State) (stale : live state = false) :
    guardedSize live scale draw size state = .error none := by
  simp [guardedSize, guardedGeneration, stale]

/-- A normal scale result that retires its owner never reaches the draw. -/
theorem guardedSize_revised (live : State → Bool)
    (draw : Nat → State → Except Cause (Value × State)) (size effective : Nat)
    (state next : State) (before : live state = true) (after : live next = false) :
    guardedSize live (fun _ _ => .ok (effective, next)) draw size state = .error none := by
  simp [guardedSize, guardedGeneration, before, after]

/-- A scale callback's original exception survives without a later draw. -/
theorem guardedSize_cause (live : State → Bool)
    (draw : Nat → State → Except Cause (Value × State)) (size : Nat)
    (state : State) (cause : Cause) (before : live state = true) :
    guardedSize live (fun _ _ => .error cause) draw size state = .error (some cause) := by
  simp [guardedSize, guardedGeneration, before]

/-- Stable scaling delegates once at exactly the resulting state and size. -/
theorem guardedSize_admitted (live : State → Bool)
    (draw : Nat → State → Except Cause (Value × State)) (size effective : Nat)
    (state next : State) (before : live state = true) (after : live next = true) :
    guardedSize live (fun _ _ => .ok (effective, next)) draw size state =
      guardedGeneration live (draw effective) next := by
  simp [guardedSize, guardedGeneration, before, after]

/-- The bounded length offset is chosen once. The random implementation remains
an explicit premise; no uniform-distribution assertion is required here. -/
def collectionWidth (minimum offset : Nat) : Nat := minimum + offset

/-- Every admitted length lies between the declared inclusive bounds. -/
theorem collectionWidth_bounds (minimum maximum size offset : Nat)
    (bounds : minimum ≤ maximum) (chosen : offset ≤ min size (maximum - minimum)) :
    minimum ≤ collectionWidth minimum offset ∧ collectionWidth minimum offset ≤ maximum := by
  simp only [collectionWidth]
  have upper := Nat.le_trans chosen (Nat.min_le_right size (maximum - minimum))
  omega

/-- Positive minimum forces an element, regardless of the chosen offset. -/
theorem collectionWidth_positive (minimum offset : Nat) (positive : 0 < minimum) :
    0 < collectionWidth minimum offset := by simp [collectionWidth]; omega

/-- Size zero admits only the minimum, preserving nonempty lower bounds. -/
theorem collectionWidth_zero_size (minimum maximum offset : Nat)
    (chosen : offset ≤ min 0 (maximum - minimum)) :
    collectionWidth minimum offset = minimum := by simp [collectionWidth] at *; omega

/-- Common collection leaves contain element ownership exactly when every
admitted result uses an element. Optional selection acquires leaves later. -/
def collectionSources (minimum : Nat) (elements : List Source) : List Source :=
  if minimum = 0 then [] else elements

/-- Mandatory collections retain exactly their declared element sources. -/
theorem collectionSources_positive (minimum : Nat) (elements : List Source)
    (positive : 0 < minimum) : collectionSources minimum elements = elements := by
  simp [collectionSources, Nat.ne_of_gt positive]

/-- An empty-capable producer does not claim unselected element ownership. -/
theorem collectionSources_optional (elements : List Source) :
    collectionSources 0 elements = [] := rfl

/-- A sized producer's explicit owner and common element leaves jointly admit.
Source identity union uses the existing generator law rather than nested guards. -/
theorem collectionSources_current [DecidableEq Source] (live : Source → Bool)
    (owner elements : List Source) (minimum : Nat) :
    (mergeSources owner (collectionSources minimum elements)).all live = true ↔
      owner.all live = true ∧ (collectionSources minimum elements).all live = true :=
  mergeSources_current live owner (collectionSources minimum elements)

/-- An obsolete mandatory source suppresses the length stage and all dependent
work. Already performed callback effects are outside the rollback claim. -/
theorem collectionSources_stale (live : State → Source → Bool) (elements : List Source)
    (minimum : Nat) (state : State) (positive : 0 < minimum)
    (stale : elements.all (live state) = false)
    (run : State → Except Cause (Value × State)) :
    guardedGeneration (fun current => (collectionSources minimum elements).all (live current))
      run state = .error none := by
  apply guardedGeneration_preflight
  simpa [collectionSources_positive minimum elements positive] using stale

/-- Common source capture cannot alter a successful pure run's returned state. -/
theorem collectionSources_admitted (live : State → Source → Bool)
    (elements : List Source) (minimum : Nat) (state next : State) (value : Value)
    (before : (collectionSources minimum elements).all (live state) = true)
    (after : (collectionSources minimum elements).all (live next) = true) :
    guardedGeneration (fun current => (collectionSources minimum elements).all (live current))
      (fun _ => (.ok (value, next) : Except Cause (Value × State))) state = .ok (value, next) := by
  exact guardedGeneration_state _ state next value before after

end LeanPoo.Functional.PropertyTesting
