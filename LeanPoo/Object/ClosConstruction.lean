-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosConstruction

/-- Logical class membership is available during initialization. Unbound slots
remain distinct from values; neither membership nor binding proves completion. -/
structure Instance (Value : Type) where
  identity : Nat
  classId : Nat
  generation : Nat
  revision : Nat
  slots : Nat → Option Value

structure Ticket where
  identity : Nat
  classId : Nat
  generation : Nat
  revision : Nat
  deriving DecidableEq

def ticket (x : Instance Value) : Ticket :=
  ⟨x.identity, x.classId, x.generation, x.revision⟩

def allocate (identity classId generation : Nat) : Instance Value :=
  ⟨identity, classId, generation, 0, fun _ => none⟩

theorem allocation_keeps_slots_unbound (i c g name : Nat) :
    (allocate (Value := Value) i c g).slots name = none := rfl

/-- The existing Slot normalizer runs before the callback-free cell batch.
Failure leaves that cell and its revision unchanged, not external effects. -/
def write (old : Instance Value) (name : Nat) (value : Value)
    (normalize : Value → Except Error Value) : Instance Value × Except Error Value :=
  match normalize value with
  | .error e => (old, .error e)
  | .ok checked =>
    ({ old with
         revision := old.revision + 1
         slots := fun key => if key = name then some checked else old.slots key }, .ok checked)

theorem refused_write_retains_instance (old : Instance Value) (name : Nat)
    (value : Value) (normalize : Value → Except Error Value) (e : Error)
    (failed : normalize value = .error e) :
    (write old name value normalize).1 = old := by simp [write, failed]

theorem checked_write_installs_normalized_value (old : Instance Value) (name : Nat)
    (value checked : Value) (normalize : Value → Except Error Value)
    (accepted : normalize value = .ok checked) :
    (write old name value normalize).1.slots name = some checked ∧
    (write old name value normalize).1.identity = old.identity := by
  simp [write, accepted]

/-- A constructor validates after the complete initializer method combination.
The checker is the existing Class/Slot protocol, not a second evaluator. -/
structure Completed (Value : Type) where
  receiver : Instance Value
  stamp : Ticket
  initialized : Bool
  valid : Bool

def publish (prepared : Completed Value) : Option (Instance Value) :=
  if prepared.initialized && prepared.valid &&
     decide (prepared.stamp = ticket prepared.receiver)
  then some prepared.receiver else none

theorem membership_alone_cannot_publish (x : Instance Value) :
    publish ⟨x, ticket x, false, true⟩ = none := by simp [publish]

theorem final_check_required (x : Instance Value) :
    publish ⟨x, ticket x, true, false⟩ = none := by simp [publish]

theorem publish_preserves_identity (p : Completed Value) (result : Instance Value)
    (accepted : publish p = some result) : result.identity = p.receiver.identity := by
  unfold publish at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

theorem callback_edit_rejects_old_check (old next : Instance Value)
    (changed : ticket old ≠ ticket next) :
    publish ⟨next, ticket old, true, true⟩ = none := by
  simp [publish, changed]

theorem completed_unbound_slot_is_legal (i c g : Nat) :
    publish ⟨allocate (Value := Value) i c g,
      ticket (allocate (Value := Value) i c g), true, true⟩ =
      some (allocate i c g) := by simp [publish]

/-- Unrequested native lazy slots are untouched by allocation and checking
metadata. Explicit initforms remain effects of the initializer, not allocation. -/
theorem allocation_does_not_run_initializer (i c g : Nat)
    (_initform : Unit → Value) :
    (allocate (Value := Value) i c g).revision = 0 ∧
    (allocate (Value := Value) i c g).slots 0 = none := by
  simp [allocate]

/-- The symbol-specialized default method resolves and re-enters the same
GF. It cannot substitute the allocation primitive for class dispatch. -/
def namedDefault (resolve : Name → Class) (generic : Class → Result)
    (name : Name) : Result := generic (resolve name)

theorem class_name_reenters_generic (resolve : Name → Class)
    (generic : Class → Result) (name : Name) :
    namedDefault resolve generic name = generic (resolve name) := rfl

end LeanPoo.Object.ClosConstruction
