-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.OwnedSlotSource

/-! Original stock constructors may run at birth. Their raw records remain
private until a reference is handed out. This separates physical allocation
from reachability and does not move constructor effects to reflection. -/
namespace LeanPoo.Object.SourceExposure

open SlotPreparation SourcePreparation

structure Heap (Self Value : Type) where
  captured : Array (CapturedBinding.Spec Self Value)
  fields : Nat → Option (CapturedBinding.Spec Self Value)
  published : Nat → Bool
  exposed : Bool

def allocate {Self Value : Type} (recipes : Array (Recipe Self Value)) : Heap Self Value :=
  let captured := recipes.map Recipe.capture
  ⟨captured, fun index => captured[index]?, fun _ => false, false⟩

def Invariant {Self Value : Type} (heap : Heap Self Value) : Prop :=
  (∀ index, heap.published index = false → heap.fields index = heap.captured[index]?) ∧
  (heap.exposed = false → ∀ index, heap.published index = false)

/-- Return the existing raw address, never call a constructor again. Mark
exposure before the address becomes available to a caller or visitor. -/
def expose {Self Value : Type} (heap : Heap Self Value) (index : Nat) :
    Option (Heap Self Value × Nat) :=
  match heap.fields index with
  | none => none
  | some _ => some ({ heap with
      exposed := true
      published := fun query => if query = index then true else heap.published query }, index)

/-- The caller needs a published reference. This is reference reachability,
not a cooperative check of the private source marker by the MOP writer. -/
def write {Self Value : Type} (heap : Heap Self Value) (index : Nat)
    (payload : CapturedBinding.Spec Self Value) : Option (Heap Self Value) :=
  if heap.published index = true then
    match heap.fields index with
    | none => none
    | some _ => some { heap with fields := fun query =>
        if query = index then some payload else heap.fields query }
  else none

def issue {Self Value : Type} (heap : Heap Self Value) :
    Option (Array (CapturedBinding.Spec Self Value)) :=
  if heap.exposed then none else some heap.captured

theorem allocate_invariant {Self Value : Type} (recipes : Array (Recipe Self Value)) :
    Invariant (allocate recipes) := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem expose_invariant {Self Value : Type} (before after : Heap Self Value)
    (index address : Nat) (valid : Invariant before)
    (step : expose before index = some (after, address)) : Invariant after := by
  unfold expose at step
  split at step
  · cases step
  · cases step
    constructor
    · intro query unpublished
      by_cases same : query = index
      · simp [same] at unpublished
      · simp [same] at unpublished
        exact valid.1 query unpublished
    · intro closed
      contradiction

theorem write_invariant {Self Value : Type} (before after : Heap Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value) (valid : Invariant before)
    (step : write before index payload = some after) : Invariant after := by
  unfold write at step
  split at step
  · rename_i published
    split at step
    · cases step
    · cases step
      constructor
      · intro query unpublished
        by_cases same : query = index
        · subst query
          rw [published] at unpublished
          contradiction
        · simpa [same] using valid.1 query unpublished
      · exact valid.2
  · cases step

inductive Reachable {Self Value : Type} (recipes : Array (Recipe Self Value)) :
    Heap Self Value → Prop where
  | allocated : Reachable recipes (allocate recipes)
  | exposed {before after index address} : Reachable recipes before →
      expose before index = some (after, address) → Reachable recipes after
  | written {before after index payload} : Reachable recipes before →
      write before index payload = some after → Reachable recipes after

theorem Reachable.invariant {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {heap : Heap Self Value} (path : Reachable recipes heap) : Invariant heap := by
  induction path with
  | allocated => exact allocate_invariant recipes
  | exposed _ step ih => exact expose_invariant _ _ _ _ ih step
  | written _ step ih => exact write_invariant _ _ _ _ ih step

/-- A complete ordinary capture can read private physical records. While no
reference has escaped, every such field equals the retained private recipe. -/
theorem issued_private_fields_exact {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {heap : Heap Self Value}
    (path : Reachable recipes heap) (captured : Array (CapturedBinding.Spec Self Value))
    (issued : issue heap = some captured) (index : Nat) :
    heap.fields index = captured[index]? := by
  unfold issue at issued
  split at issued
  · cases issued
  · rename_i closed
    have privateSource : heap.exposed = false := Bool.eq_false_iff.mpr closed
    cases issued
    exact path.invariant.1 index (path.invariant.2 privateSource index)

theorem closed_write_impossible {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {heap : Heap Self Value}
    (path : Reachable recipes heap) (closed : heap.exposed = false)
    (index : Nat) (payload : CapturedBinding.Spec Self Value) :
    write heap index payload = none := by
  simp [write, path.invariant.2 closed index]

/-- Physical allocation is permitted without an external reference. This
distinction preserves the original stock constructor's observation point. -/
theorem private_record_control :
    let heap : Heap Unit Nat := allocate #[.constant 7]
    heap.fields 0 = some (.constant 7) ∧ heap.published 0 = false ∧
      issue heap = some heap.captured ∧ write heap 0 (.constant 9) = none := by
  simp [allocate, Recipe.capture, issue, write]

/-- Project published addresses to OwnedSlotSource's raw map. This projection
concerns capture/field data; its ticket protocol owns epochs separately. -/
def project {Self Value : Type} (heap : Heap Self Value) (identity : Nat) :
    OwnedSlotSource.Source Self Value :=
  ⟨identity, heap.captured, heap.exposed, 0, none,
    fun index => if heap.published index then heap.fields index else none⟩

theorem issue_projection {Self Value : Type} (heap : Heap Self Value) (identity : Nat) :
    OwnedSlotSource.issue (project heap identity) = issue heap := rfl

theorem projection_invariant {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {heap : Heap Self Value}
    (path : Reachable recipes heap) (identity : Nat) :
    OwnedSlotSource.Invariant (project heap identity) := by
  intro closed
  refine ⟨rfl, ?_⟩
  intro index
  simp [project, path.invariant.2 closed index]

/-- A view's index stores ordinals, not raw references. Its storage/index may
be shared by retained views; reading names alone publishes no address. -/
def enumerate {Key Self Value : Type} (heap : Heap Self Value) (rows : List (Key × Nat)) :
    Heap Self Value × List Key := (heap, rows.map Prod.fst)

def reflectKey {Key Self Value : Type} [DecidableEq Key]
    (heap : Heap Self Value) (rows : List (Key × Nat)) (key : Key) :
    Heap Self Value × Option (CapturedBinding.Spec Self Value) :=
  match rows.lookup key with
  | none => (heap, none)
  | some index =>
    match expose heap index with
    | none => (heap, none)
    | some (after, address) => (after, heap.fields address)

theorem names_publish_no_reference {Key Self Value : Type}
    (heap : Heap Self Value) (rows : List (Key × Nat)) :
    (enumerate heap rows).1 = heap := rfl

theorem missing_key_keeps_source {Key Self Value : Type} [DecidableEq Key]
    (heap : Heap Self Value) (rows : List (Key × Nat)) (key : Key)
    (missing : rows.lookup key = none) :
    reflectKey heap rows key = (heap, none) := by simp [reflectKey, missing]

/-- The original field is returned, with exposure already committed. No new
constructor, replacement raw record or business evaluation is introduced. -/
theorem hit_commits_before_delivery {Key Self Value : Type} [DecidableEq Key]
    (heap : Heap Self Value) (rows : List (Key × Nat)) (key : Key) (index : Nat)
    (payload : CapturedBinding.Spec Self Value) (hit : rows.lookup key = some index)
    (field : heap.fields index = some payload) :
    reflectKey heap rows key =
      ({ heap with exposed := true
                   published := fun query => if query = index then true else heap.published query },
       some payload) := by
  simp [reflectKey, hit, expose, field]

theorem hit_revokes_new_issue {Key Self Value : Type} [DecidableEq Key]
    (heap : Heap Self Value) (rows : List (Key × Nat)) (key : Key) (index : Nat)
    (payload : CapturedBinding.Spec Self Value) (hit : rows.lookup key = some index)
    (field : heap.fields index = some payload) :
    issue (reflectKey heap rows key).1 = none := by
  rw [hit_commits_before_delivery heap rows key index payload hit field]
  rfl

end LeanPoo.Object.SourceExposure
