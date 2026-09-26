/-!
One shared executable fixed point. Lean is strict and does not tie recursive
values directly, so a private reference cell connects a delayed self handle
to the one thunk that computes the result. The cell never escapes this
constructor. The computation may still diverge if it forces self too early.
-/

namespace LeanPoo.Prototype

/-- Tie one recursive thunk without rebuilding `compute` at every use. -/
unsafe def sharedFix {α : Type} (compute : Thunk α → α) : Thunk α :=
  unsafeBaseIO do
    let rec unavailable : Thunk α := Thunk.mk fun _ => unavailable.get
    let cell ← IO.mkRef unavailable
    let self : Thunk α := Thunk.mk fun _ => (unsafeBaseIO cell.get).get
    let result : Thunk α := Thunk.mk fun _ => compute self
    cell.set result
    return result

end LeanPoo.Prototype
