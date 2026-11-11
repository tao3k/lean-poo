-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.SourcePreparation

/-! Raw SlotSpecs are allocated only on exposure. Ordinary raw field writes do
not notify a source, advance its revision, or repair its private marker. -/
namespace LeanPoo.Object.OwnedSlotSource

open SlotPreparation SourcePreparation

structure Source (Self Value : Type) where
  identity : Nat
  captured : Array (CapturedBinding.Spec Self Value)
  exposed : Bool
  epoch : Nat
  pending : Option (Nat × Nat)
  raw : Nat → Option (CapturedBinding.Spec Self Value)

structure Ticket where
  source : Nat
  epoch : Nat
  index : Nat
  deriving DecidableEq

def allocate {Self Value : Type} (recipes : Array (Recipe Self Value)) (seed : Nat) :
    Source Self Value :=
  ⟨seed, recipes.map Recipe.capture, false, 0, none, fun _ => none⟩

/-- Thread fresh allocation identity; a Module ID or view name is not a
storage allocation identity. The native adapter uses its actual allocation. -/
def allocateFresh {Self Value : Type} (recipes : Array (Recipe Self Value)) (seed : Nat) :
    Source Self Value × Nat := (allocate recipes seed, seed + 1)

theorem fresh_allocations_distinct {Self Value : Type}
    (left right : Array (Recipe Self Value)) (seed : Nat) :
    (allocateFresh left seed).1.identity ≠
      (allocateFresh right (allocateFresh left seed).2).1.identity := by
  simp [allocateFresh, allocate]

/-- A private source has no raw objects to mutate and no author construction
in flight. This is derived from the allocation/operation sequence below. -/
def Invariant {Self Value : Type} (source : Source Self Value) : Prop :=
  source.exposed = false → source.pending = none ∧ ∀ index, source.raw index = none

def issue {Self Value : Type} (source : Source Self Value) :
    Option (Array (CapturedBinding.Spec Self Value)) :=
  if source.exposed then none else some source.captured

/-- Repeated reflection first returns an existing raw address unchanged.
Only a genuinely missing, in-range raw cell reserves a constructor call. The
exposure bit is committed BEFORE that call, including callbacks or failure. -/
def reserve {Self Value : Type} (source : Source Self Value) (index : Nat) :
    Option (Source Self Value × Ticket) :=
  if index < source.captured.size ∧ (source.raw index).isNone then
    let next := source.epoch + 1
    some ({ source with exposed := true, epoch := next, pending := some (next, index) },
      ⟨source.identity, next, index⟩)
  else none

/-- Publish the actual constructor result, not a successful purity claim.
An exposed source never uses this raw result to issue a private capture. -/
def finish {Self Value : Type} (source : Source Self Value) (ticket : Ticket)
    (payload : CapturedBinding.Spec Self Value) : Option (Source Self Value) :=
  if ticket.source = source.identity ∧ ticket.epoch = source.epoch ∧
      source.pending = some (ticket.epoch, ticket.index) ∧ source.exposed = true ∧
      ticket.index < source.captured.size ∧ (source.raw ticket.index).isNone then
    some { source with
      epoch := source.epoch + 1
      pending := none
      raw := fun index => if index = ticket.index then some payload else source.raw index }
  else none

/-- Failure abandons the pending result without restoring private status.
The constructor may already have performed effects. -/
def abort {Self Value : Type} (source : Source Self Value) : Source Self Value :=
  { source with epoch := source.epoch + 1, pending := none }

/-- A raw MOP writer needs an actually allocated raw object. It changes ONLY
that payload: no fictitious source notification or generation bump is assumed. -/
def rawWrite {Self Value : Type} (source : Source Self Value) (index : Nat)
    (payload : CapturedBinding.Spec Self Value) : Option (Source Self Value) :=
  match source.raw index with
  | none => none
  | some _ => some { source with
      raw := fun query => if query = index then some payload else source.raw query }

def readField {Self Value : Type} (source : Source Self Value) (index : Nat) :
    Option (CapturedBinding.Spec Self Value) :=
  match source.raw index with
  | some payload => some payload
  | none => source.captured[index]?

/-- The index denotes one actual published raw record. Field updates keep its
address; reflection first reuses this address instead of running a constructor. -/
def rawAddress {Self Value : Type} (source : Source Self Value) (index : Nat) :
    Option (Nat × Nat) :=
  (source.raw index).map fun _ => (source.identity, index)

theorem allocation_invariant {Self Value : Type} (recipes : Array (Recipe Self Value))
    (seed : Nat) : Invariant (allocate recipes seed) := by
  intro _
  exact ⟨rfl, fun _ => rfl⟩

theorem reserve_exposes {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (ticket : Ticket) (step : reserve source index = some (next, ticket)) :
    next.exposed = true ∧ next.captured = source.captured := by
  unfold reserve at step
  split at step
  · cases step; exact ⟨rfl, rfl⟩
  · cases step

theorem reserve_revokes_before_constructor {Self Value : Type}
    (source next : Source Self Value) (index : Nat) (ticket : Ticket)
    (step : reserve source index = some (next, ticket)) : issue next = none := by
  simp [issue, (reserve_exposes source next index ticket step).1]

theorem finish_exposed {Self Value : Type} (source next : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value)
    (step : finish source ticket payload = some next) :
    next.exposed = true ∧ next.captured = source.captured := by
  unfold finish at step
  split at step
  · rename_i accepted
    cases step
    exact ⟨accepted.2.2.2.1, rfl⟩
  · cases step

theorem raw_write_keeps_metadata {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (step : rawWrite source index payload = some next) :
    next.captured = source.captured ∧ next.exposed = source.exposed ∧
      next.epoch = source.epoch ∧ next.pending = source.pending := by
  unfold rawWrite at step
  split at step
  · cases step
  · cases step; exact ⟨rfl, rfl, rfl, rfl⟩

theorem raw_write_invariant {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value) (valid : Invariant source)
    (step : rawWrite source index payload = some next) : Invariant next := by
  unfold rawWrite at step
  split at step
  · cases step
  · rename_i old present
    cases step
    intro closed
    have absent := (valid closed).2 index
    rw [absent] at present
    contradiction

inductive Reachable {Self Value : Type} (recipes : Array (Recipe Self Value))
    (seed : Nat) : Source Self Value → Prop where
  | allocated : Reachable recipes seed (allocate recipes seed)
  | reserved {before after index ticket} : Reachable recipes seed before →
      reserve before index = some (after, ticket) → Reachable recipes seed after
  | finished {before after ticket payload} : Reachable recipes seed before →
      finish before ticket payload = some after → Reachable recipes seed after
  | aborted {before} : Reachable recipes seed before → Reachable recipes seed (abort before)
  | written {before after index payload} : Reachable recipes seed before →
      rawWrite before index payload = some after → Reachable recipes seed after

theorem Reachable.invariant {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source) :
    Invariant source := by
  induction path with
  | allocated => exact allocation_invariant recipes seed
  | reserved _ step _ =>
    intro closed
    have exposed := (reserve_exposes _ _ _ _ step).1
    simp [exposed] at closed
  | finished _ step _ =>
    intro closed
    have exposed := (finish_exposed _ _ _ _ step).1
    simp [exposed] at closed
  | aborted _ ih =>
    intro closed
    exact ⟨rfl, (ih closed).2⟩
  | written _ step ih => exact raw_write_invariant _ _ _ _ ih step

theorem Reachable.capture_unchanged {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {seed : Nat} {source : Source Self Value}
    (path : Reachable recipes seed source) : source.captured = recipes.map Recipe.capture := by
  induction path with
  | allocated => rfl
  | reserved _ step ih => exact (reserve_exposes _ _ _ _ step).2.trans ih
  | finished _ step ih => exact (finish_exposed _ _ _ _ step).2.trans ih
  | aborted _ ih => exact ih
  | written _ step ih => exact (raw_write_keeps_metadata _ _ _ _ step).1.trans ih

/-- This rejects a raw write because no raw address exists, not because a raw
writer cooperatively checks a private exposure flag. -/
theorem closed_has_no_raw_write {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {seed : Nat} {source : Source Self Value}
    (path : Reachable recipes seed source) (closed : source.exposed = false)
    (index : Nat) (payload : CapturedBinding.Spec Self Value) :
    rawWrite source index payload = none := by
  simp [rawWrite, (path.invariant closed).2 index]

theorem issued_capture_exact {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source)
    (captured : Array (CapturedBinding.Spec Self Value))
    (issued : issue source = some captured) (index : Nat) :
    readField source index = captured[index]? := by
  unfold issue at issued
  split at issued
  · cases issued
  · rename_i closed
    have privateSource : source.exposed = false := Bool.eq_false_iff.mpr closed
    cases issued
    simp [readField, (path.invariant privateSource).2 index]

/-- Derive sibling installation callability from the actual generator forms.
No Slot body is evaluated and no user assertion of purity is trusted. -/
theorem issued_callable {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source)
    (captured : Array (CapturedBinding.Spec Self Value))
    (issued : issue source = some captured) (index : Nat)
    (payload : CapturedBinding.Spec Self Value) (found : captured[index]? = some payload) :
    CapturedBinding.classified payload = true := by
  have same : captured = source.captured := by
    unfold issue at issued
    split at issued
    · cases issued
    · cases issued; rfl
  rw [same, path.capture_unchanged] at found
  simp only [Array.getElem?_map] at found
  cases atIndex : recipes[index]? with
  | none => simp [atIndex] at found
  | some recipe =>
    simp only [atIndex, Option.map_some, Option.some.injEq] at found
    cases found
    exact recipe.callable

theorem stale_finish_refused {Self Value : Type} (source : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value)
    (stale : ticket.epoch ≠ source.epoch) : finish source ticket payload = none := by
  simp [finish, stale]

theorem foreign_finish_refused {Self Value : Type} (source : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value)
    (foreign : ticket.source ≠ source.identity) : finish source ticket payload = none := by
  simp [finish, foreign]

theorem aborted_finish_refused {Self Value : Type} (source : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value) :
    finish (abort source) ticket payload = none := by
  simp [finish, abort]

theorem pending_index_mismatch_refused {Self Value : Type} (source : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value)
    (different : source.pending ≠ some (ticket.epoch, ticket.index)) :
    finish source ticket payload = none := by
  simp [finish, different]

theorem reserve_ticket {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (ticket : Ticket) (step : reserve source index = some (next, ticket)) :
    ticket.source = source.identity ∧ ticket.epoch = source.epoch + 1 ∧
      next.epoch = ticket.epoch ∧ next.pending = some (ticket.epoch, ticket.index) := by
  unfold reserve at step
  split at step
  · cases step; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases step

/-- A second reservation is a structural source operation. It supersedes the
first ticket; raw MOP payload writes, in contrast, do not report such an epoch. -/
theorem second_reservation_retires_ticket {Self Value : Type}
    (source next : Source Self Value) (oldTicket newTicket : Ticket) (index : Nat)
    (oldCurrent : oldTicket.epoch = source.epoch)
    (step : reserve source index = some (next, newTicket))
    (payload : CapturedBinding.Spec Self Value) : finish next oldTicket payload = none := by
  have fact := reserve_ticket source next index newTicket step
  apply stale_finish_refused
  omega

theorem finish_retires_ticket {Self Value : Type} (source next : Source Self Value)
    (ticket : Ticket) (payload : CapturedBinding.Spec Self Value)
    (step : finish source ticket payload = some next) :
    finish next ticket payload = none := by
  unfold finish at step
  split at step
  · rename_i accepted
    cases step
    apply stale_finish_refused
    change ticket.epoch ≠ source.epoch + 1
    omega
  · cases step

theorem absent_raw_write_refused {Self Value : Type} (source : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (absent : source.raw index = none) : rawWrite source index payload = none := by
  simp [rawWrite, absent]

theorem raw_write_visible {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (step : rawWrite source index payload = some next) :
    readField next index = some payload := by
  unfold rawWrite at step
  split at step
  · cases step
  · cases step; simp [readField]

theorem raw_write_keeps_addresses {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (step : rawWrite source index payload = some next) (query : Nat) :
    rawAddress next query = rawAddress source query := by
  unfold rawWrite at step
  split at step
  · cases step
  · rename_i old found
    cases step
    by_cases same : query = index
    · simp [rawAddress, same, found]
    · simp [rawAddress, same]

theorem existing_raw_not_reconstructed {Self Value : Type} (source : Source Self Value)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (found : source.raw index = some payload) :
    reserve source index = none ∧ rawAddress source index = some (source.identity, index) := by
  simp [reserve, rawAddress, found]

/-- Failed reflection cannot reactivate an old private capture approval. -/
theorem abort_keeps_exposure {Self Value : Type} (source : Source Self Value)
    (exposed : source.exposed = true) : issue (abort source) = none := by
  simp [issue, abort, exposed]

private def originalThunk : CapturedBinding.Spec Unit Nat :=
  .thunk (.procedure (fun _ => 7))
private def original : Source Unit Nat := allocate #[.thunk (fun _ => 7)] 0
private def requested : Source Unit Nat :=
  { original with exposed := true, epoch := 1, pending := some (1, 0) }
private def requestTicket : Ticket := ⟨0, 1, 0⟩
private def materialized : Source Unit Nat :=
  { requested with
    epoch := 2
    pending := none
    raw := fun index => if index = 0 then some originalThunk else none }
private def modified : Source Unit Nat :=
  { materialized with raw := fun index =>
      if index = 0 then some (.thunk .nonCallable) else none }

/-- A real same-variant thunk field edit is visible to future ordinary capture.
No raw object exists before reflection; the old immutable cut remains valid
for a receiver that already captured it. Raw writes do not advance epochs. -/
theorem exposure_raw_write_control :
    rawWrite original 0 (.thunk .nonCallable) = none ∧
    reserve original 0 = some (requested, requestTicket) ∧
    issue requested = none ∧
    finish requested requestTicket originalThunk = some materialized ∧
    rawWrite materialized 0 (.thunk .nonCallable) = some modified ∧
    modified.epoch = materialized.epoch ∧
    modified.captured = original.captured ∧
    (readField modified 0).map CapturedBinding.classified = some false ∧
    (original.captured[0]?).map CapturedBinding.classified = some true ∧
    issue modified = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [rawWrite, original, allocate, requested, requestTicket, issue, reserve,
      finish, materialized, modified, originalThunk, Recipe.capture, readField,
      CapturedBinding.classified, CapturedBinding.Target.callable]
  funext query
  by_cases same : query = 0 <;> simp [same]

/-- An in-flight result cannot overwrite another reserved index in the same
source, and failure cannot make the source private again. -/
theorem replacement_and_failure_control :
    let source : Source Unit Nat := allocate #[.constant 7, .constant 9] 4
    let first := { source with exposed := true, epoch := 1, pending := some (1, 0) }
    let second := { first with epoch := 2, pending := some (2, 1) }
    reserve source 0 = some (first, ⟨4, 1, 0⟩) ∧
    reserve first 1 = some (second, ⟨4, 2, 1⟩) ∧
    finish second ⟨4, 1, 0⟩ (.constant 7) = none ∧
    finish second ⟨4, 2, 0⟩ (.constant 7) = none ∧
    issue (abort second) = none ∧
    finish (abort second) ⟨4, 2, 1⟩ (.constant 9) = none := by
  simp [allocate, reserve, finish, issue, abort]

end LeanPoo.Object.OwnedSlotSource
