import LeanPoo.Proof.Object
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

private def compared : Object.Cache (next.prepare [false, true]) next.state :=
  Proof.rebaseInstanceCacheByValue current next [false, true]
    (fun _ _ => inferInstance) oldCache

#guard oldCache.peek false == some (some 10)
#guard oldCache.peek true == some (some 20)
#guard reused.peek false == some (some 10)
#guard reused.peek true == none
#guard (reused.read true).1 == some 30
#guard compared.peek false == some (some 10)
#guard compared.peek true == none

example : (reused.read false).1 = next.state false := by
  rw [reused.read_sound, (next.prepare [false, true]).resolve_sound]
  exact next.agrees false

namespace ComputedDependency

private def declaration (changed : Nat) : Object.Declaration Bool Values :=
  Object.Declaration.empty
    |>.withValue true changed
    |>.withSlot false (.self fun self => (self true).map (· + 1))

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

private def ranked (changed : Nat) : Object.Ranked Bool Values (plan changed) :=
  { rank := fun key => if key then 0 else 1
    dependsOnLower := by
      intro key left right lower
      cases key with
      | false =>
          change (left true).map (· + 1) = (right true).map (· + 1)
          rw [lower true (by decide)]
      | true => rfl }

private def current : Object.Instance Bool Values (plan 20) :=
  (ranked 20).instantiate

private def next : Object.Instance Bool Values (plan 30) :=
  (ranked 30).instantiate

-- Both the edited slot and its computed dependent changed value.
private def patch : Proof.Patch Bool (fun key => Option (Values key)) :=
  Proof.Patch.setMany [⟨true, some 30⟩, ⟨false, some 31⟩]

private theorem aligned : next.state = patch.apply current.state := by
  funext key
  cases key <;> native_decide

private def oldCache : Object.Cache (current.prepare [false, true]) current.state :=
  (current.cache [false, true]).force [false, true]

private def reused : Object.Cache (next.prepare [false, true]) next.state :=
  Proof.rebaseInstanceCache current next patch aligned
    [false, true] oldCache

private def compared : Object.Cache (next.prepare [false, true]) next.state :=
  Proof.rebaseInstanceCacheByValue current next [false, true]
    (fun _ _ => inferInstance) oldCache

#guard oldCache.peek false == some (some 21)
#guard oldCache.peek true == some (some 20)
#guard reused.peek false == none
#guard reused.peek true == none
#guard (reused.read false).1 == some 31
#guard compared.peek false == none
#guard compared.peek true == none

private def relation : Proof.Obligation Bool (fun key => Option (Values key)) :=
  { dependencies := [false, true]
    holds := fun state => state false = (state true).map (· + 1)
    stable := by
      intro before after equal holds
      calc
        after false = before false := (equal false (by simp)).symm
        _ = (before true).map (· + 1) := holds
        _ = (after true).map (· + 1) := by rw [equal true (by simp)] }

private def certified : Proof.CertifiedObject Bool Values (plan 20) :=
  { instanceValue := current
    obligations := [relation]
    certificate := by
      intro obligation member
      have same : obligation = relation := by
        simpa [Proof.proofObjectOfInstance] using member
      subst obligation
      change relation.holds current.state
      change current.state false = (current.state true).map (· + 1)
      native_decide }

private def revised : Proof.CertifiedObject Bool Values (plan 30) :=
  certified.applyPatch patch next aligned (by
    intro obligation member
    rcases (Proof.mem_pending_iff _ _ _).mp member with old | fresh
    · have same : obligation = relation := by
        simpa [certified, Proof.proofObjectOfInstance] using old.1
      subst obligation
      change relation.holds next.state
      change next.state false = (next.state true).map (· + 1)
      native_decide
    · simp [patch, Proof.Patch.setMany] at fresh)

example : relation.holds revised.instanceValue.state :=
  revised.certificate relation (by
    change relation ∈ [relation] ++ []
    simp)

end ComputedDependency
