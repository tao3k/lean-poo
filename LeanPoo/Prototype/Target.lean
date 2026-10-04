import LeanPoo.Prototype.Object

/-! The four target-update policies described in chapter 9. Rejecting an
update is the default. The other policies are explicitly named because
retaining, replacing, or discarding the specification changes extension. -/

namespace LeanPoo.Prototype

universe u v

inductive TargetUpdateError where
  | forbidden
  deriving Repr, BEq, DecidableEq

/-- Raw target updates are rejected by default. This does not execute the
change or force the target; specification-level edits remain available. -/
def Object.updateTarget (_object : Object Self Parent) (_change : Self → Self) :
    Except TargetUpdateError (Object Self Parent) :=
  .error .forbidden

theorem Object.updateTarget_forbidden (object : Object Self Parent)
    (change : Self → Self) :
    object.updateTarget change = .error .forbidden := rfl

/-- Deliberately replace the target while retaining the original prototype.
A later extension recomposes that prototype and loses this target-only edit. -/
def Object.updateTargetOutOfSync (object : Object Self Parent)
    (change : Self → Self) : Object Self Parent :=
  { object with result := Thunk.mk fun _ => change object.value }

theorem Object.updateTargetOutOfSync_prototype (object : Object Self Parent)
    (change : Self → Self) :
    (object.updateTargetOutOfSync change).prototype = object.prototype := rfl

theorem Object.updateTargetOutOfSync_base (object : Object Self Parent)
    (change : Self → Self) :
    (object.updateTargetOutOfSync change).base = object.base := rfl

/-- Replace the specification with a constant updated target. It remains
extensible but inherited formulas are no longer rebound to a later self.
The shared thunk delays the update until the target is actually requested. -/
def Object.overwriteTargetSpecification (object : Object Self Parent)
    (change : Self → Self) : Object Self Parent :=
  let target := Thunk.mk fun _ => change object.value
  { prototype := fun _ _ => target.get
    base := object.base
    result := target }

/-- The replacement prototype returns exactly its retained target and does
not depend on a future self or inherited computation. -/
theorem Object.overwriteTargetSpecification_constant
    (object : Object Self Parent) (change : Self → Self)
    (self : Thunk Self) (inherited : Thunk Parent) :
    (object.overwriteTargetSpecification change).prototype self inherited =
      (object.overwriteTargetSpecification change).value := rfl

/-- Keep only the updated target thunk. The result carries no retained
prototype or inheritance metadata and has no object-extension operation. -/
def Object.detachTarget (object : Object Self Parent)
    (change : Self → Self) : Thunk Self :=
  Thunk.mk fun _ => change object.value

theorem Object.detachTarget_matches_outOfSync
    (object : Object Self Parent) (change : Self → Self) :
    (object.detachTarget change).get =
      (object.updateTargetOutOfSync change).value := rfl

end LeanPoo.Prototype
