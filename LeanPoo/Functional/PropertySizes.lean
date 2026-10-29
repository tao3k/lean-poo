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

end LeanPoo.Functional.PropertyTesting
