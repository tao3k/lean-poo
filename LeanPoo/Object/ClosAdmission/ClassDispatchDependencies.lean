-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosClassPublication
import LeanPoo.Object.ClosAdmission.DispatchInvalidation

namespace LeanPoo.Object.ClosAdmission.ClassDispatchDependencies
open LeanPoo.Functional.StrongComponents (Reach)
open LeanPoo.Functional.LocalSccRegion (Edge)
open LeanPoo.Object.ClosAdmission.PublishedDispatch (Affected)

inductive Scope where
  | roster
  | whole
  deriving DecidableEq

/-- The existing reverse index points from source to consumer. An ordinary
edge opens for every edit. A C4 edge to an assigned projection does not
open for a direct subclass-roster assignment. -/
structure Dependencies (n : Nat) where
  ordinary : Edge n
  c4 : Edge n

def Dependencies.opens (d : Dependencies n) : Scope → Edge n
  | .roster => d.ordinary
  | .whole => fun source consumer => d.ordinary source consumer || d.c4 source consumer

/-- Only the first edge can use the direct edit's scope. A return edge
can reach the source again, now with an unrestricted incoming edit. -/
inductive Propagated (d : Dependencies n) (scope : Scope) (root : Fin n) : Fin n → Prop
  | first {child} : d.opens scope root child = true → Propagated d scope root child
  | next {source child} : Propagated d scope root source →
      d.opens .whole source child = true → Propagated d scope root child

def AffectedBy (d : Dependencies n) (edits : Fin n → Option Scope) (owner : Fin n) : Prop :=
  ∃ root scope, edits root = some scope ∧ (owner = root ∨ Propagated d scope root owner)

theorem propagated_iff (d : Dependencies n) (scope : Scope) (root owner : Fin n) :
    Propagated d scope root owner ↔
      ∃ first, d.opens scope root first = true ∧ Reach (d.opens .whole) first owner := by
  constructor
  · intro path
    induction path with
    | @first child edge => exact ⟨child, edge, .refl child⟩
    | @next source child _ edge ih =>
      obtain ⟨first, entered, suffix⟩ := ih
      exact ⟨first, entered, suffix.trans (.step edge (.refl child))⟩
  · rintro ⟨first, edge, suffix⟩
    have appendPath {source destination} (path : Reach (d.opens .whole) source destination) :
        Propagated d scope root source → Propagated d scope root destination := by
      induction path with
      | refl => exact id
      | step selected _ ih => exact fun entered => ih (.next entered selected)
    exact appendPath suffix (.first edge)

theorem whole_edit_exact (d : Dependencies n) (root owner : Fin n) :
    (owner = root ∨ Propagated d .whole root owner) ↔ Reach (d.opens .whole) root owner := by
  rw [propagated_iff]
  constructor
  · rintro (rfl | ⟨_, edge, suffix⟩)
    · exact .refl _
    · exact .step edge suffix
  · intro path
    cases path with
    | refl => exact .inl rfl
    | step edge suffix => exact .inr ⟨_, edge, suffix⟩

theorem whole_roots_are_existing_reverse_closure (d : Dependencies n) (dirty : Fin n → Bool)
    (owner : Fin n) :
    AffectedBy d (fun root => if dirty root then some .whole else none) owner ↔
      Affected (d.opens .whole) (fun root => dirty root = true) owner := by
  constructor
  · rintro ⟨root, scope, selected, path⟩
    by_cases changed : dirty root = true
    · have scopeEq : Scope.whole = scope := by simpa [changed] using selected
      subst scope
      exact ⟨root, changed, (whole_edit_exact d root owner).mp path⟩
    · simp [changed] at selected
  · rintro ⟨root, changed, path⟩
    exact ⟨root, .whole, by simp [changed], (whole_edit_exact d root owner).mpr path⟩

/-- A direct roster assignment keeps the receiver in the affected set for
ordinary reads. A different consumer is affected exactly when some
ordinary first edge opens a path to it. -/
theorem direct_roster_exact (d : Dependencies n) (root plan : Fin n) (distinct : plan ≠ root) :
    (plan = root ∨ Propagated d .roster root plan) ↔
      ∃ next, d.ordinary root next = true ∧ Reach (d.opens .whole) next plan := by
  simpa [distinct, Dependencies.opens] using
    (propagated_iff d .roster root plan)

theorem roster_preserves_plan_epoch (d : Dependencies n) (root plan : Fin n)
    (distinct : plan ≠ root)
    (noRoute : ∀ next, Reach (d.opens .whole) next plan → d.ordinary root next = false) :
    ¬ (plan = root ∨ Propagated d .roster root plan) := by
  rw [direct_roster_exact d root plan distinct]
  rintro ⟨next, opened, suffix⟩
  rw [noRoute next suffix] at opened
  contradiction

theorem propagated_root_widens (d : Dependencies n) (scope : Scope)
    (root alreadyVisited plan : Fin n)
    (reentered : Propagated d scope root alreadyVisited)
    (edge : d.opens .whole alreadyVisited plan = true) :
    Propagated d scope root plan := .next reentered edge

/-- Two registrations on one pair retain the union of their admitted
edits. None denotes the ordinary (unrestricted) edge. -/
def joinExclusions [DecidableEq Slot] (left right : Option Slot) : Option Slot :=
  if left = right then left else none

theorem joined_edge_opens [DecidableEq Slot] (left right : Option Slot) (edit : Slot) :
    joinExclusions left right ≠ some edit ↔ left ≠ some edit ∨ right ≠ some edit := by
  by_cases same : left = right
  · subst right
    simp [joinExclusions]
  · have cannotBoth : left ≠ some edit ∨ right ≠ some edit := by
      by_cases h : left = some edit
      · exact .inr fun r => same (h.trans r.symm)
      · exact .inl h
    simp [joinExclusions, same, cannotBoth]

/-- The assigned Class projection, including the prototype, C4 order, and
generation identity, supplies the same inputs to every pure dispatch stage. -/
theorem subclass_registration_preserves_preparation
    (world : LeanPoo.Object.ClosClassPublication.World)
    (updates : Nat → Option (List Nat))
    (prepare : (Nat → LeanPoo.Object.ClosClassPublication.Layout) → Recipe) :
    prepare (LeanPoo.Object.ClosClassPublication.publish world ⟨fun _ => none, updates⟩).layout =
      prepare world.layout :=
  congrArg prepare
    (LeanPoo.Object.ClosClassPublication.subclass_bookkeeping_preserves_layout world updates)

end LeanPoo.Object.ClosAdmission.ClassDispatchDependencies
