import LeanPoo.Prototype.SharedCell

/-!
One shared executable fixed point. Lean is strict and does not tie recursive
values directly, so a private reference cell connects a delayed self handle
to the one thunk that computes the result. The cell never escapes this
constructor. The computation may still diverge if it forces self too early.
-/

namespace LeanPoo.Prototype

private structure PrivateCell (α : Type) where
  cell : IO.Ref (Thunk α)
  unavailable : Thunk α

private def notify (observer : Option (SharedCell.Event → BaseIO Unit))
    (event : SharedCell.Event) : BaseIO Unit :=
  match observer with
  | none => pure ()
  | some observe => observe event

/-- Diagnostic forcing must precede its completion callback. A native
primitive consumes the value before the next IO action; a pure `let` can be
sunk past the callback by the compiler. This box is not the recursive cell. -/
private def demand (value : α) : BaseIO α := do
  let box ← IO.mkRef value
  box.get

/-- Backend for the source-owned constructor program. Observation hooks are
optional and do not run in the ordinary constructor. No native proof is returned. -/
@[inline] private unsafe def ioOperations {α : Type} (compute : Thunk α → α)
    (observer : Option (SharedCell.Event → BaseIO Unit)) :
    SharedCell.Operations BaseIO (PrivateCell α) (Thunk α) where
  unavailable := do
    let rec unavailable : Thunk α := Thunk.mk fun _ => unavailable.get
    notify observer .mkUnavailable
    return unavailable
  mkRef := fun unavailable => do
    let cell ← IO.mkRef unavailable
    notify observer .mkRef
    if observer.isSome then
      notify observer (.verify (ptrEq (← cell.get) unavailable))
    return ⟨cell, unavailable⟩
  mkSelf := fun cell => do
    let self : Thunk α := Thunk.mk fun _ => unsafeBaseIO do
      notify observer .beginSelf
      let current ← cell.cell.get
      if observer.isSome then
        notify observer (.getRef (if ptrEq current cell.unavailable then .unavailable else .result))
      let value ← if observer.isSome then demand current.get else pure current.get
      notify observer .returnSelf
      return value
    notify observer .mkSelf
    return self
  mkResult := fun self => do
    let result : Thunk α := Thunk.mk fun _ => unsafeBaseIO do
      notify observer .beginResult
      let value ← if observer.isSome then demand (compute self) else pure (compute self)
      notify observer .returnResult
      return value
    notify observer .mkResult
    return result
  setRef := fun cell result => do
    cell.cell.set result
    notify observer (.setRef .result)
    if observer.isSome then
      notify observer (.verify (ptrEq (← cell.cell.get) result))

/-- Tie one recursive thunk without rebuilding `compute` at every use. -/
unsafe def sharedFix {α : Type} (compute : Thunk α → α) : Thunk α :=
  unsafeBaseIO (SharedCell.tie (ioOperations compute none))

/-- A native observation adapter over the same constructor and primitives.
The callback records data. Completed gets are acknowledged after native return. -/
structure ObservedThunk (α : Type) where
  result : Thunk α
  observer : SharedCell.Event → BaseIO Unit

unsafe def ObservedThunk.get (thunk : ObservedThunk α) : BaseIO α := do
  let value ← demand thunk.result.get
  thunk.observer .forceResult
  return value

unsafe def sharedFixWithObserver {α : Type} (compute : (Unit → α) → α)
    (observe : SharedCell.Event → BaseIO Unit) : BaseIO (ObservedThunk α) := do
  let adapted := fun self : Thunk α => compute fun _ => unsafeBaseIO do
    let value ← demand self.get
    observe .forceSelf
    return value
  let result ← SharedCell.tie (ioOperations adapted (some observe))
  return ⟨result, observe⟩

end LeanPoo.Prototype
