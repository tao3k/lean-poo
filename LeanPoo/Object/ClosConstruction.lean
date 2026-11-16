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
  currentGeneration : Nat

def publish (prepared : Completed Value) : Option (Instance Value) :=
  if prepared.initialized && prepared.valid &&
     decide (prepared.stamp = ticket prepared.receiver) &&
     decide (prepared.receiver.generation = prepared.currentGeneration)
  then some prepared.receiver else none

theorem membership_alone_cannot_publish (x : Instance Value) :
    publish ⟨x, ticket x, false, true, x.generation⟩ = none := by simp [publish]

theorem final_check_required (x : Instance Value) :
    publish ⟨x, ticket x, true, false, x.generation⟩ = none := by simp [publish]

theorem publish_preserves_identity (p : Completed Value) (result : Instance Value)
    (accepted : publish p = some result) : result.identity = p.receiver.identity := by
  unfold publish at accepted
  split at accepted
  · cases accepted; rfl
  · contradiction

theorem callback_edit_rejects_old_check (old next : Instance Value)
    (changed : ticket old ≠ ticket next) :
    publish ⟨next, ticket old, true, true, next.generation⟩ = none := by
  simp [publish, changed]

/-- Class redefinition can advance the schema before the stored instance layout.
A native Slot read does not run the mutating migration protocol implicitly. -/
def readCurrent (x : Instance Value) (currentGeneration name : Nat) : Option (Option Value) :=
  if x.generation = currentGeneration then some (x.slots name) else none

theorem outdated_layout_cannot_publish (x : Instance Value) (current : Nat)
    (outdated : x.generation ≠ current) :
    publish ⟨x, ticket x, true, true, current⟩ = none := by
  simp [publish, outdated]

theorem outdated_read_does_not_expose_old_slot (x : Instance Value) (current name : Nat)
    (outdated : x.generation ≠ current) : readCurrent x current name = none := by
  simp [readCurrent, outdated]

theorem current_read_keeps_unbound_distinct (x : Instance Value) (name : Nat) :
    readCurrent x x.generation name = some (x.slots name) := by simp [readCurrent]

theorem completed_unbound_slot_is_legal
 (i c g : Nat) :
    publish ⟨allocate (Value := Value) i c g,
      ticket (allocate (Value := Value) i c g), true, true, g⟩ =
      some (allocate i c g) := by simp [publish, allocate]

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

variable {Value : Type}

/-- Absence is metadata, not an invented top-type declaration. The host Slot
protocol accepts untyped values; an explicitly declared constraint is retained. -/
def effectiveConstraint (checks : List (Value → Bool)) : Option (Value → Bool) :=
  match checks with
  | [] => none
  | _ :: _ => some (fun value => checks.all (fun check => check value))

def accepts (constraint : Option (Value → Bool)) (value : Value) : Bool :=
  match constraint with
  | none => true
  | some check => check value

theorem absent_type_has_no_synthetic_descriptor :
    effectiveConstraint (Value := Value) [] = none := rfl

theorem effective_constraint_checks_all (checks : List (Value → Bool)) (value : Value) :
    accepts (effectiveConstraint checks) value = checks.all (fun check => check value) := by
  cases checks <;> rfl

theorem omitted_child_preserves_inherited_constraints
    (inherited : List (Value → Bool)) :
    effectiveConstraint ([] ++ inherited) = effectiveConstraint inherited := rfl

theorem child_cannot_weaken_parent (child inherited : List (Value → Bool)) (value : Value)
    (accepted : accepts (effectiveConstraint (child ++ inherited)) value = true) :
    accepts (effectiveConstraint inherited) value = true := by
  simp only [effective_constraint_checks_all, List.all_append, Bool.and_eq_true] at accepted
  simpa only [effective_constraint_checks_all] using accepted.2

theorem inherited_rejection_survives_untyped_child
    (inherited : List (Value → Bool)) (value : Value)
    (refused : accepts (effectiveConstraint inherited) value = false) :
    accepts (effectiveConstraint ([] ++ inherited)) value = false := refused

end LeanPoo.Object.ClosConstruction

