import LeanPoo.Proof.Object

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
  { nodes := [{ name := "Base" }] }

private def declaration (changed : Nat) : Object.Declaration Bool Values :=
  Object.Declaration.empty
    |>.withValue false 10
    |>.withValue true changed

private def schema (changed : Nat) : Object.Schema Bool Values :=
  { graph
    declaration := fun name =>
      if name == "Base" then some (declaration changed) else none }

private def plan (changed : Nat) : Object.Plan Bool Values :=
  { schema := schema changed
    root := "Base"
    precedence := ["Base"]
    valid := by
      change C4.linearize graph "Base" = .ok ["Base"]
      native_decide }

private def current : Object.Instance Bool Values (plan 20) :=
  { state := fun key => if key then some 20 else some 10
    agrees := by
      intro key
      cases key <;> native_decide }

private def next : Object.Instance Bool Values (plan 30) :=
  { state := fun key => if key then some 30 else some 10
    agrees := by
      intro key
      cases key <;> native_decide }

private def patch : Proof.Patch Bool (fun key => Option (Values key)) :=
  Proof.Patch.set true (some 30)

private theorem aligned : next.state = patch.apply current.state := by
  funext key
  cases key <;> rfl

private def oldCache : Object.Cache (current.prepare [false, true]) current.state :=
  (current.cache [false, true]).force [false, true]

private def reused : Object.Cache (next.prepare [false, true]) next.state :=
  Proof.rebaseInstanceCache current next patch aligned
    [false, true] oldCache

#guard oldCache.peek false == some (some 10)
#guard oldCache.peek true == some (some 20)
#guard reused.peek false == some (some 10)
#guard reused.peek true == none
#guard (reused.read true).1 == some 30

example : (reused.read false).1 = next.state false := by
  rw [reused.read_sound, (next.prepare [false, true]).resolve_sound]
  exact next.agrees false
