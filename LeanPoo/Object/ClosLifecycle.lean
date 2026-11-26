-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later

namespace LeanPoo.Object.ClosLifecycle

inductive Operation where
  | make | reinitialize | redefine | changeClass
  deriving DecidableEq, Repr

inductive Generic where
  | allocate | initialize | reinitialize | shared | redefine | changeClass
  deriving DecidableEq, Repr

structure Signature (Key : Type) where
  keys : List Key
  allowOther : Bool

-- Only signatures of applicable methods are supplied, separately for each
-- generic and its actual required arguments (including the shared slot mask).
def invocations : Operation → List Generic
  | .make => [.allocate, .initialize, .shared]
  | .reinitialize => [.reinitialize, .shared]
  | .redefine => [.redefine, .shared]
  | .changeClass => [.changeClass, .shared]

def signatures (op : Operation) (applicable : Generic → List (Signature Key)) :
    List (Signature Key) :=
  (invocations op).flatMap applicable

inductive Admission where
  | malformed | unknown | accepted
  deriving DecidableEq, Repr

def admit [BEq Key] (op : Operation) (slots : List Key)
    (applicable : Generic → List (Signature Key)) (tail : Option (List Key))
    (allowInCall : Bool) : Admission :=
  match tail with
  | none => .malformed
  | some names =>
    let methods := signatures op applicable
    if allowInCall || methods.any (·.allowOther) ||
        names.all (fun name =>
          slots.contains name || methods.any (fun method => method.keys.contains name))
    then .accepted else .unknown

theorem local_admission [BEq Key] (op : Operation) (slots : List Key)
    (before after : Generic → List (Signature Key))
    (same : ∀ g ∈ invocations op, before g = after g)
    (tail : Option (List Key)) (allowInCall : Bool) :
    admit op slots before tail allowInCall = admit op slots after tail allowInCall := by
  have congr {gs : List Generic} (h : ∀ g ∈ gs, before g = after g) :
      gs.flatMap before = gs.flatMap after := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.flatMap_cons]
      rw [h g (by simp), ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]
  cases tail <;> simp [admit, signatures, congr same]

theorem reinitialize_key_does_not_enter_make (key : Nat) :
    admit .make [] (fun g => if g = .reinitialize then [⟨[key], false⟩] else [])
        (some [key]) false = .unknown ∧
    admit .reinitialize []
        (fun g => if g = .reinitialize then [⟨[key], false⟩] else [])
        (some [key]) false = .accepted := by simp [admit, signatures, invocations]

theorem allocate_key_enters_make (key : Nat) :
    admit .make [] (fun g => if g = .allocate then [⟨[key], false⟩] else [])
        (some [key]) false = .accepted := by simp [admit, signatures, invocations]

theorem malformed_precedes_allowance [BEq Key] (op : Operation) (slots : List Key)
    (applicable : Generic → List (Signature Key)) :
    admit op slots applicable none true = .malformed := rfl

inductive SlotMask (Slot : Type) where
  | all | only (names : List Slot)
  deriving DecidableEq, Repr

def slotMask (op : Operation) (added : List Slot) : SlotMask Slot :=
  match op with
  | .make => .all
  | .reinitialize => .only []
  | .redefine | .changeClass => .only added

def fills [BEq Slot] (mask : SlotMask Slot) (slot : Slot) (supplied bound : Bool) : Bool :=
  supplied || (!bound && match mask with
    | .all => true
    | .only names => names.contains slot)

theorem reinitialize_fills_only_explicit [BEq Slot] (slot : Slot) (added : List Slot)
    (supplied bound : Bool) :
    fills (slotMask .reinitialize added) slot supplied bound = supplied := by
  simp [fills, slotMask]

theorem supplied_ignores_slot_mask [BEq Slot] (mask : SlotMask Slot) (slot : Slot)
    (bound : Bool) : fills mask slot true bound = true := rfl

theorem change_fills_unbound_added [BEq Slot] (added : List Slot) (slot : Slot) :
    fills (slotMask .changeClass added) slot false false = added.contains slot := rfl

inductive Event (Slot Method : Type) where
  | before (method : Method)
  | primary (mask : SlotMask Slot)
  | after (method : Method)
  deriving DecidableEq, Repr

-- For a standard primary reached through next-method, execute the existing
-- combination's before/after order with one shared primary slot write phase.
def trace (admission : Admission) (op : Operation) (added : List Slot)
    (before after : List Method) : List (Event Slot Method) :=
  match admission with
  | .accepted => before.map Event.before ++
      [Event.primary (slotMask op added)] ++ after.reverse.map Event.after
  | _ => []

theorem rejected_has_no_shared_effects (failure : Admission)
    (h : failure ≠ .accepted) (op : Operation) (added : List Slot)
    (before after : List Method) :
    trace failure op added before after = [] := by cases failure <;> simp_all [trace]

theorem standard_combination_runs_after_in_reverse (op : Operation)
    (added : List Slot) (before after : List Method) :
    (trace .accepted op added before after).drop (before.length + 1) =
      after.reverse.map Event.after := by simp [trace, List.drop_append, List.drop_of_length_le]

end LeanPoo.Object.ClosLifecycle
