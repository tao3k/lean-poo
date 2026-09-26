import LeanPoo.Object.Ranked

open LeanPoo

private instance [DecidableEq α] [DecidableEq β] :
    DecidableEq (Except α β) := by
  intro x y
  cases x with
  | error left =>
      cases y with
      | error right => simpa using (inferInstance : Decidable (left = right))
      | ok _ => exact isFalse (by intro equality; cases equality)
  | ok left =>
      cases y with
      | error _ => exact isFalse (by intro equality; cases equality)
      | ok right => simpa using (inferInstance : Decidable (left = right))

private abbrev Values (_ : Bool) := Nat

private def graph : C4.Graph :=
  { nodes := [{ name := "Base" },
      { name := "Child", parentOrders := [["Base"]] }] }

private def base : Object.Declaration Bool Values :=
  Object.Declaration.empty.withValue true 20

private def child : Object.Declaration Bool Values :=
  Object.Declaration.empty.withSlot false
    (.self fun self => (self true).map (· + 1))

private def schema : Object.Schema Bool Values :=
  { graph
    declaration := fun name =>
      if name == "Base" then some base
      else if name == "Child" then some child else none }

private def plan : Object.Plan Bool Values :=
  { schema
    root := "Child"
    precedence := ["Child", "Base"]
    valid := by
      change C4.linearize graph "Child" = .ok ["Child", "Base"]
      native_decide }

/-- The computed false slot reads only true, which has smaller rank. -/
private def ranked : Object.Ranked Bool Values plan :=
  { rank := fun key => if key then 0 else 1
    dependsOnLower := by
      intro key left right lower
      cases key with
      | false =>
          change (left true).map (· + 1) = (right true).map (· + 1)
          rw [lower true (by decide)]
      | true => rfl }

private def dependencies : Object.Dependencies Bool Values plan :=
  { keys := [false, true]
    reads := fun key => if key then [] else [true]
    supported := by intro key dependency membership; cases key <;> simp
    dependsOnlyOn := by
      intro key left right equal
      cases key with
      | false =>
          change (left true).map (· + 1) = (right true).map (· + 1)
          rw [equal true (by simp)]
      | true => rfl }

private def inferred : Except (Object.DependencyError Bool)
    (Object.Instance Bool Values plan) :=
  dependencies.inferRanked.map Object.Ranked.instantiate

#guard match inferred with
  | .ok instanceValue =>
      instanceValue.state true == some 20 &&
      instanceValue.state false == some 21
  | .error _ => false

private def cyclic : Object.Dependencies Bool Values plan :=
  { keys := [false, true]
    reads := fun key => if key then [false] else [true]
    supported := by intro key dependency membership; cases key <;> simp
    dependsOnlyOn := by
      intro key left right equal
      cases key with
      | false =>
          change (left true).map (· + 1) = (right true).map (· + 1)
          rw [equal true (by simp)]
      | true => rfl }

#guard match cyclic.inferRanked with
  | .error (.blocked remaining) => remaining == [false, true]
  | _ => false

private def missingSource : Object.Dependencies Bool Values plan :=
  { keys := [false]
    reads := fun key => if key then [] else [true]
    supported := by
      intro key dependency membership
      cases key with
      | false => simp
      | true => simp at membership
    dependsOnlyOn := by
      intro key left right equal
      cases key with
      | false =>
          change (left true).map (· + 1) = (right true).map (· + 1)
          rw [equal true (by simp)]
      | true => rfl }

#guard match missingSource.inferRanked with
  | .error (.blocked remaining) => remaining == [false]
  | _ => false

private def object : Object.Instance Bool Values plan :=
  ranked.instantiate

#guard object.state true == some 20
#guard object.state false == some 21

private def cache : Object.Cache (object.prepare [false, true]) object.state :=
  (object.cache [false, true]).force [false, true]

#guard cache.peek false == some (some 21)

example : plan.resolve false object.state = some 21 := by
  rw [object.agrees]
  native_decide

example : (cache.read false).1 = object.state false :=
  object.cachedRead [false, true] cache false
