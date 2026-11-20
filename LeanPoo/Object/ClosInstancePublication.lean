-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosInstancePublication

structure Layout (Storage : Type) where
  classId : Nat
  generation : Nat
  storage : Storage
  deriving DecidableEq

structure Instance (Storage : Type) where
  identity : Nat
  revision : Nat
  layout : Layout Storage

-- Admission may have external effects. Refusal preserves the instance,
-- not those effects. Publication uses the existing serial callback-free batch.
structure Prepared (Storage Error Effects : Type) where
  effects : Effects
  result : Except Error (Layout Storage)

def commit (old : Instance Storage) (next : Layout Storage) : Instance Storage :=
  { old with revision := old.revision + 1, layout := next }

def publish (old : Instance Storage) (prepared : Prepared Storage Error Effects) :
    Instance Storage × Effects × Except Error Unit :=
  match prepared.result with
  | .error error => (old, prepared.effects, .error error)
  | .ok next => (commit old next, prepared.effects, .ok ())

theorem refusal_preserves_layout_and_revision (old : Instance Storage)
    (prepared : Prepared Storage Error Effects) (error : Error)
    (refused : prepared.result = .error error) :
    (publish old prepared).1 = old := by
  simp [publish, refused]

theorem publication_retains_external_effects (old : Instance Storage)
    (prepared : Prepared Storage Error Effects) :
    (publish old prepared).2.1 = prepared.effects := by
  cases result : prepared.result <;> simp [publish, result]

theorem success_publishes_all_fields (old : Instance Storage)
    (prepared : Prepared Storage Error Effects) (next : Layout Storage)
    (accepted : prepared.result = .ok next) :
    (publish old prepared).1.layout = next ∧
    (publish old prepared).1.revision = old.revision + 1 ∧
    (publish old prepared).1.identity = old.identity := by
  simp [publish, accepted, commit]

inductive Point where
  | preparation
  | afterPublication

def observe (old : Instance Storage) (next : Layout Storage) : Point → Instance Storage
  | .preparation => old
  | .afterPublication => commit old next

theorem read_precheck_sees_one_layout (old : Instance Storage) (next : Layout Storage)
    (point : Point) :
    (observe old next point).layout = old.layout ∨
    (observe old next point).layout = next := by
  cases point <;> simp [observe, commit]

-- User initialization starts after commit. Its refusal does not roll back a
-- published layout, and a reentrant reader receives the complete new instance.
def invokeUpdate (old : Instance Storage) (next : Layout Storage)
    (callback : Instance Storage → Except Error Result) :
    Instance Storage × Except Error Result :=
  let current := commit old next
  (current, callback current)

theorem update_observes_committed_instance (old : Instance Storage) (next : Layout Storage)
    (callback : Instance Storage → Except Error Result) :
    invokeUpdate old next callback = (commit old next, callback (commit old next)) := rfl

theorem update_refusal_keeps_committed_layout (old : Instance Storage) (next : Layout Storage)
    (callback : Instance Storage → Except Error Result) :
    (invokeUpdate old next callback).1.layout = next := rfl

-- Writing class before reading its generation exposes this intermediate state
-- to a metadata read precheck. The atomic model has no such observation point.
theorem sequential_class_write_exposes_mixed_layout :
    let old : Layout (List Nat) := ⟨0, 0, [10]⟩
    let next : Layout (List Nat) := ⟨1, 1, [20]⟩
    let mixed := { old with classId := next.classId }
    mixed ≠ old ∧ mixed ≠ next := by decide

end LeanPoo.Object.ClosInstancePublication
