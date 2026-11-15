-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosClassPublication

abbrev ClassId := Nat
abbrev Generation := Nat

structure Slot where
  name : Nat
  classAllocated : Bool
  initargs : List Nat
  deriving DecidableEq

structure Projection where
  prototype : Nat
  parents : List ClassId
  precedence : List ClassId
  effective : List Slot

structure Layout extends Projection where
  generation : Generation
  lookup : Nat → Option Slot
  history : Generation → Option (List Slot)

def lookupSlot (slots : List Slot) (name : Nat) : Option Slot :=
  slots.find? (fun slot => slot.name == name)

def Layout.complete (layout : Layout) : Prop :=
  layout.lookup = lookupSlot layout.effective

-- The published generation owns one projection. History records only
-- the effective descriptors needed by instances at an earlier generation.
def nextLayout (old : Layout) (candidate : Projection) : Layout :=
  { toProjection := candidate
    generation := old.generation + 1
    lookup := lookupSlot candidate.effective
    history := fun generation =>
      if generation = old.generation then some old.effective
      else old.history generation }

structure World where
  layout : ClassId → Layout
  subclasses : ClassId → List ClassId

structure Plan where
  layout : ClassId → Option Projection
  subclasses : ClassId → Option (List ClassId)

-- Staging may read or refuse before this step. The serial Scheme batch
-- first prepares every write and then publishes without reader callbacks.
def publish (world : World) (plan : Plan) : World :=
  { layout := fun cls =>
      match plan.layout cls with
      | none => world.layout cls
      | some candidate => nextLayout (world.layout cls) candidate
    subclasses := fun cls => (plan.subclasses cls).getD (world.subclasses cls) }

inductive ObservationPoint where
  | staging
  | published

def observe (before : World) (plan : Plan) : ObservationPoint → World
  | .staging => before
  | .published => publish before plan

theorem staging_sees_one_world (before : World) (plan : Plan) :
    observe before plan .staging = before := rfl

theorem selected_class_publishes_entire_projection (before : World) (plan : Plan)
    (cls : ClassId) (candidate : Projection) (selected : plan.layout cls = some candidate) :
    ((publish before plan).layout cls).toProjection = candidate ∧
    ((publish before plan).layout cls).generation = (before.layout cls).generation + 1 ∧
    ((publish before plan).layout cls).lookup = lookupSlot candidate.effective := by
  simp [publish, selected, nextLayout]

theorem other_class_preserves_layout (before : World) (plan : Plan)
    (cls : ClassId) (unselected : plan.layout cls = none) :
    (publish before plan).layout cls = before.layout cls := by
  simp [publish, unselected]

theorem related_subclass_edges_share_the_publication (before : World) (plan : Plan)
    (cls : ClassId) (children : List ClassId) (selected : plan.subclasses cls = some children) :
    (observe before plan .published).subclasses cls = children := by
  simp [observe, publish, selected]

theorem observed_layout_is_complete (before : World) (plan : Plan)
    (oldComplete : ∀ cls, (before.layout cls).complete) (point : ObservationPoint) :
    ∀ cls, ((observe before plan point).layout cls).complete := by
  intro cls
  cases point with
  | staging => exact oldComplete cls
  | published =>
    cases selected : plan.layout cls with
    | none => simpa [observe, publish, selected] using oldComplete cls
    | some projection => simp [observe, publish, selected, nextLayout, Layout.complete]

def Layout.slotsAt (layout : Layout) (generation : Generation) : Option (List Slot) :=
  if generation = layout.generation then some layout.effective else layout.history generation

theorem existing_instance_finds_its_layout (old : Layout) (candidate : Projection) :
    (nextLayout old candidate).slotsAt old.generation = some old.effective := by
  simp [Layout.slotsAt, nextLayout]

theorem earlier_instance_keeps_its_layout (old : Layout) (candidate : Projection)
    (generation : Generation) (earlier : generation < old.generation) :
    (nextLayout old candidate).slotsAt generation = old.slotsAt generation := by
  simp [Layout.slotsAt, nextLayout, Nat.ne_of_lt earlier,
    Nat.ne_of_lt (Nat.lt_trans earlier (Nat.lt_succ_self old.generation))]

-- Scheme Slot reads detach the list spine and seal each generated descriptor.
-- Editing a public list therefore changes only the caller's projection.
def inspect (layout : Layout) : List Slot := layout.effective

theorem reflection_can_be_edited_without_replacing_layout (layout : Layout)
    (edit : List Slot → List Slot) :
    (let snapshot := edit (inspect layout); (layout, snapshot)).1 = layout := rfl

end LeanPoo.Object.ClosClassPublication
