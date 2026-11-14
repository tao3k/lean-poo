-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.SlotPreparation

/-! Constructor-owned source capture, raw exposure and supported writer coverage.
This is a POO preparation contract, not another evaluator or cache. -/
namespace LeanPoo.Object.SourcePreparation

open SlotPreparation

/-- The four forms actually emitted by object/init. A thunk is constructed
from a procedure, not an arbitrary raw SlotSpec payload. Bodies are opaque
and never invoked by production, exposure, issuance or the writer below. -/
inductive Recipe (Self Value : Type) where
  | constant (value : Value)
  | thunk (body : Unit → Value)
  | self (body : Self → Value)
  | computed (body : Self → CapturedBinding.Target Value → Value)

def Recipe.capture {Self Value : Type} : Recipe Self Value → CapturedBinding.Spec Self Value
  | .constant value => .constant value
  | .thunk body => .thunk (.procedure body)
  | .self body => .self body
  | .computed body => .computed body

/-- Derive callable installation from the producer's constructors. This says
nothing about body success, dynamic declarations, hooks or arbitrary raw input. -/
theorem Recipe.callable {Self Value : Type} (recipe : Recipe Self Value) :
    CapturedBinding.classified recipe.capture = true := by
  cases recipe <;> rfl

structure Handle where
  source : Nat
  index : Nat
  deriving DecidableEq

/-- One source's captured data and its raw exposure/write state. Heap stores
only writes; an unchanged raw field reads the producer's original payload.
Native correspondence must use fresh source identity and mark exposure BEFORE
returning any original SlotSpec. This is source storage, not business caching. -/
structure Source (Self Value : Type) where
  identity : Nat
  captured : Array (CapturedBinding.Spec Self Value)
  exposed : List Nat
  writes : Nat → Option (CapturedBinding.Spec Self Value)

/-- Actual supported writer coverage, not a caller-supplied purity flag. -/
def Invariant {Self Value : Type} (source : Source Self Value) : Prop :=
  ∀ index, index ∉ source.exposed → source.writes index = none

def allocate {Self Value : Type} (recipes : Array (Recipe Self Value)) (next : Nat) :
    Source Self Value × Nat :=
  (⟨next, recipes.map Recipe.capture, [], fun _ => none⟩, next + 1)

theorem allocation_invariant {Self Value : Type}
    (recipes : Array (Recipe Self Value)) (next : Nat) :
    Invariant (allocate recipes next).1 := by
  intro index _
  rfl

def expose {Self Value : Type} (source : Source Self Value) (index : Nat) :
    Option (Source Self Value × Handle) :=
  if index < source.captured.size then
    some ({ source with exposed := index :: source.exposed }, ⟨source.identity, index⟩)
  else none

/-- Raw mutation does NOT advance the containing object revision. It requires
the exact source's previously exposed handle; foreign/stale handles refuse. -/
def write {Self Value : Type} (source : Source Self Value) (handle : Handle)
    (payload : CapturedBinding.Spec Self Value) : Option (Source Self Value) :=
  if handle.source = source.identity ∧ handle.index ∈ source.exposed then
    some { source with writes := fun index =>
      if index = handle.index then some payload else source.writes index }
  else none

theorem exposure_invariant {Self Value : Type} (source next : Source Self Value)
    (index : Nat) (handle : Handle) (valid : Invariant source)
    (step : expose source index = some (next, handle)) : Invariant next := by
  unfold expose at step
  split at step
  · cases step
    intro query separate
    exact valid query (fun member => separate (List.mem_cons_of_mem _ member))
  · cases step

theorem exposure_keeps_producer_snapshot {Self Value : Type}
    (source next : Source Self Value) (index : Nat) (handle : Handle)
    (step : expose source index = some (next, handle)) :
    next.captured = source.captured ∧ next.identity = source.identity := by
  unfold expose at step
  split at step
  · cases step
    exact ⟨rfl, rfl⟩
  · cases step

theorem write_invariant {Self Value : Type} (source next : Source Self Value)
    (handle : Handle) (payload : CapturedBinding.Spec Self Value)
    (valid : Invariant source) (step : write source handle payload = some next) :
    Invariant next := by
  unfold write at step
  split at step
  · rename_i allowed
    cases step
    intro query separate
    have other : query ≠ handle.index := by
      intro same
      exact separate (same.symm ▸ allowed.2)
    simp only [other, ↓reduceIte]
    exact valid query separate
  · cases step

/-- A private cut comes only from unexposed state. It contains payloads, not
raw references that later field mutation could silently rewrite. -/
def issue {Self Value : Type} (source : Source Self Value) :
    Option (Array (CapturedBinding.Spec Self Value)) :=
  if source.exposed.isEmpty then some source.captured else none

def rawAt {Self Value : Type} (source : Source Self Value) (index : Nat) :
    Option (CapturedBinding.Spec Self Value) :=
  match source.writes index with
  | some payload => some payload
  | none => source.captured[index]?

/-- Derive field-by-field equivalence to ordinary capture from the concrete
writer invariant and exposure state. No equality of mutable payload reads is
assumed. PayloadCapture.capture_frame transports this equality to the complete
original ordered validation/capture schedule when the native issuer supplies it. -/
theorem issued_fields_exact {Self Value : Type} (source : Source Self Value)
    (captured : Array (CapturedBinding.Spec Self Value))
    (valid : Invariant source) (issued : issue source = some captured) (index : Nat) :
    rawAt source index = captured[index]? := by
  unfold issue at issued
  split at issued
  · rename_i closed
    cases issued
    have empty : source.exposed = [] := List.isEmpty_iff.mp closed
    have unwritten : source.writes index = none := valid index (by simp [empty])
    simp [rawAt, unwritten]
  · cases issued

theorem exposure_revokes_new_issuance {Self Value : Type}
    (source next : Source Self Value) (index : Nat) (handle : Handle)
    (step : expose source index = some (next, handle)) : issue next = none := by
  unfold expose at step
  split at step
  · cases step
    rfl
  · cases step

theorem foreign_handle_refused {Self Value : Type} (source : Source Self Value)
    (handle : Handle) (payload : CapturedBinding.Spec Self Value)
    (foreign : handle.source ≠ source.identity) : write source handle payload = none := by
  simp [write, foreign]

theorem private_handle_refused {Self Value : Type} (source : Source Self Value)
    (handle : Handle) (payload : CapturedBinding.Spec Self Value)
    (privateCell : handle.index ∉ source.exposed) : write source handle payload = none := by
  simp [write, privateCell]

/-- Previously prepared receivers keep their captured recipes. A raw write
must affect future ordinary capture, not retroactively replace that old cut. -/
theorem raw_write_keeps_producer_snapshot {Self Value : Type}
    (source next : Source Self Value) (handle : Handle)
    (payload : CapturedBinding.Spec Self Value)
    (step : write source handle payload = some next) :
    next.captured = source.captured ∧ next.identity = source.identity := by
  unfold write at step
  split at step
  · cases step
    exact ⟨rfl, rfl⟩
  · cases step

/-- An out-of-range lookup exposes no raw handle and leaves the private
source eligible. Missing input is not permission to mark arbitrary cells. -/
theorem missing_exposure_refused {Self Value : Type} (source : Source Self Value)
    (index : Nat) (outside : source.captured.size ≤ index) : expose source index = none := by
  simp [expose, Nat.not_lt.mpr outside]

/-- Reachability derives writer coverage from the real operation sequence.
It cannot be supplied by labeling a mutable foreign source as private. -/
inductive Reachable {Self Value : Type} (recipes : Array (Recipe Self Value))
    (seed : Nat) : Source Self Value → Prop where
  | allocated : Reachable recipes seed (allocate recipes seed).1
  | exposed {before after index handle} : Reachable recipes seed before →
      expose before index = some (after, handle) → Reachable recipes seed after
  | written {before after handle payload} : Reachable recipes seed before →
      write before handle payload = some after → Reachable recipes seed after

theorem Reachable.invariant {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source) :
    Invariant source := by
  induction path with
  | allocated => exact allocation_invariant recipes seed
  | exposed _ step ih => exact exposure_invariant _ _ _ _ ih step
  | written _ step ih => exact write_invariant _ _ _ _ ih step

theorem Reachable.producer_capture {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source) :
    source.captured = recipes.map Recipe.capture := by
  induction path with
  | allocated => rfl
  | exposed _ step ih => exact (exposure_keeps_producer_snapshot _ _ _ _ step).1.trans ih
  | written _ step ih => exact (raw_write_keeps_producer_snapshot _ _ _ _ step).1.trans ih

/-- No generated sibling can hide an installation-time non-callable payload.
Derive this from actual construction/reachable edits, not an approval Boolean. -/
theorem Reachable.capture_callable {Self Value : Type} {recipes : Array (Recipe Self Value)}
    {seed : Nat} {source : Source Self Value} (path : Reachable recipes seed source)
    (index : Nat) (payload : CapturedBinding.Spec Self Value)
    (found : source.captured[index]? = some payload) :
    CapturedBinding.classified payload = true := by
  rw [path.producer_capture] at found
  simp only [Array.getElem?_map] at found
  cases atIndex : recipes[index]? with
  | none => simp [atIndex] at found
  | some recipe =>
    simp only [atIndex, Option.map_some, Option.some.injEq] at found
    cases found
    exact recipe.callable

/-- Production pays the one normalization pass. Issuance returns the retained
array itself; it must not rebuild/map the complete catalog per request. -/
theorem issue_borrows_capture {Self Value : Type} (source : Source Self Value)
    (closed : source.exposed = []) : issue source = some source.captured := by
  simp [issue, closed]

theorem reachable_issued_fields_exact {Self Value : Type}
    {recipes : Array (Recipe Self Value)} {seed : Nat} {source : Source Self Value}
    (path : Reachable recipes seed source)
    (captured : Array (CapturedBinding.Spec Self Value))
    (issued : issue source = some captured) (index : Nat) :
    rawAt source index = captured[index]? :=
  issued_fields_exact source captured path.invariant issued index

private def readField {Self Value : Type}
    (read : Nat → Option (CapturedBinding.Spec Self Value)) (index : Nat) :
    Except Nat (CapturedBinding.Spec Self Value) :=
  match read index with
  | some payload => .ok payload
  | none => .error index

/-- Connect the concrete writer-derived cut to the existing ordered capture
interpreter. Every scheduled field, duplicate and first missing-field error is
preserved. This does not authorize moving the schedule across an author effect. -/
theorem reachable_original_capture_exact {Key Self Value : Type} [DecidableEq Key]
    {recipes : Array (Recipe Self Value)} {seed : Nat} {source : Source Self Value}
    (path : Reachable recipes seed source)
    (captured : Array (CapturedBinding.Spec Self Value))
    (issued : issue source = some captured) (refs : List (Key × Nat)) :
    PayloadCapture.capture (Payload := fun _ => CapturedBinding.Spec Self Value)
        (fun _ index => readField (rawAt source) index) refs =
      PayloadCapture.capture (fun _ index => readField (fun position => captured[position]?) index) refs := by
  apply PayloadCapture.capture_frame
  intro ref _
  simp only [readField, reachable_issued_fields_exact path captured issued]

/-- Source identity is the native allocation identity, not an object revision.
Advancing the allocation seed makes an old raw handle foreign even when the
new source has the same shape and has exposed that same ordinal. -/
theorem old_handle_refused_by_fresh_source {Self Value : Type}
    (recipes : Array (Recipe Self Value)) (seed : Nat) (handle : Handle)
    (payload : CapturedBinding.Spec Self Value) (older : handle.source < seed)
    (exposed : Source Self Value) (index : Nat) (newHandle : Handle)
    (step : expose (allocate recipes seed).1 index = some (exposed, newHandle)) :
    write exposed handle payload = none := by
  apply foreign_handle_refused
  rw [(exposure_keeps_producer_snapshot _ _ _ _ step).2]
  exact Nat.ne_of_lt older

private def freshControl : Source Unit Nat :=
  (allocate #[Recipe.thunk (fun _ => 17)] 0).1

private def exposedControl : Source Unit Nat := { freshControl with exposed := [0] }

private def changedControl : Source Unit Nat :=
  { exposedControl with writes := fun index =>
      if index = 0 then some (.thunk .nonCallable) else none }

/-- Actual exposure and permitted raw mutation preserve the old prepared cut,
revoke new private issuance, and make future ordinary capture see refusal.
The source identity does not change, so an identity/revision-only check loses
this distinction. No body is evaluated while establishing this control. -/
theorem exposure_write_and_prepared_receiver_control :
    write freshControl ⟨0, 0⟩ (.thunk .nonCallable) = none ∧
    expose freshControl 0 = some (exposedControl, ⟨0, 0⟩) ∧
    write exposedControl ⟨0, 0⟩ (.thunk .nonCallable) = some changedControl ∧
    issue changedControl = none ∧
    rawAt changedControl 0 = some (.thunk .nonCallable) ∧
    freshControl.identity = changedControl.identity ∧
    changedControl.captured = freshControl.captured ∧
    (freshControl.captured[0]?).map CapturedBinding.classified = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | simp [freshControl, exposedControl, allocate,
      expose, Recipe.capture, CapturedBinding.classified, CapturedBinding.Target.callable]

/-- Reusing the old prepared receiver's immutable cut as evidence for a NEW
capture would accept a malformed raw thunk. Those are distinct authorities. -/
theorem old_cut_cannot_certify_new_capture :
    rawAt changedControl 0 ≠ freshControl.captured[0]? := by
  intro equal
  have classified := congrArg (Option.map CapturedBinding.classified) equal
  simp [rawAt, changedControl, exposedControl, freshControl, allocate,
    Recipe.capture, CapturedBinding.classified, CapturedBinding.Target.callable] at classified

/-- An uncovered runtime/MOP field write bypasses `expose` and `write`.
This is deliberately NOT a supported Source transition. It models the gap
that must be closed before applying this model to mutable Scheme SlotSpecs. -/
private def runtimeBypassControl : Source Unit Nat :=
  { freshControl with writes := fun index =>
      if index = 0 then some (.thunk .nonCallable) else none }

/-- Neither allocation identity nor an unexposed marker detects an uncovered
runtime write. An issuance guard using those facts alone would still pass. -/
theorem runtime_bypass_preserves_identity_and_issuance :
    runtimeBypassControl.identity = freshControl.identity ∧
    runtimeBypassControl.exposed = [] ∧
    issue runtimeBypassControl = some freshControl.captured := by
  exact ⟨rfl, rfl, rfl⟩

theorem runtime_bypass_breaks_writer_coverage : ¬ Invariant runtimeBypassControl := by
  intro covered
  have unwritten := covered 0 (by simp [runtimeBypassControl, freshControl, allocate])
  simp [runtimeBypassControl] at unwritten

/-- The original capture equivalence fails even though the naive issuance
guard succeeds. This is a concrete malformed-thunk counterexample, not an
assumption that arbitrary mutation is harmless. -/
theorem runtime_bypass_breaks_issued_field_equivalence :
    rawAt runtimeBypassControl 0 ≠ freshControl.captured[0]? := by
  intro equal
  have classified := congrArg (Option.map CapturedBinding.classified) equal
  simp [rawAt, runtimeBypassControl, freshControl, allocate, Recipe.capture,
    CapturedBinding.classified, CapturedBinding.Target.callable] at classified

/-- Reachability is a substantive native correspondence obligation. A model
that simply omits an available runtime writer does not qualify that writer. -/
theorem runtime_bypass_not_reachable
    {recipes : Array (Recipe Unit Nat)} {seed : Nat} :
    ¬ Reachable recipes seed runtimeBypassControl := by
  intro path
  exact runtime_bypass_breaks_writer_coverage path.invariant

/-- A clone/namespace view has its own identity but may retain another view's
raw storage allocation. The storage owner, not this view's identity, fences
new issuance. A composite clone registers each retained storage fragment. -/
structure View where
  identity : Nat
  owner : Nat

abbrev Storage (Self Value : Type) := Nat → Option (Source Self Value)

def View.issue {Self Value : Type} (storage : Storage Self Value) (view : View) :=
  match storage view.owner with
  | none => none
  | some source => if source.identity = view.owner then SourcePreparation.issue source else none

def View.expose {Self Value : Type} (storage : Storage Self Value) (view : View)
    (index : Nat) : Option (Storage Self Value × Handle) :=
  match storage view.owner with
  | none => none
  | some source =>
      if source.identity = view.owner then
        match SourcePreparation.expose source index with
        | none => none
        | some (next, handle) =>
            some ((fun owner => if owner = view.owner then some next else storage owner), handle)
      else none

theorem View.identity_is_not_storage_authority {Self Value : Type}
    (storage : Storage Self Value) (view : View) (identity : Nat) :
    View.issue storage { view with identity := identity } = View.issue storage view := rfl

theorem View.exposure_witness {Self Value : Type}
    (storage next : Storage Self Value) (view : View) (index : Nat) (handle : Handle)
    (step : View.expose storage view index = some (next, handle)) :
    ∃ before after, storage view.owner = some before ∧ before.identity = view.owner ∧
      SourcePreparation.expose before index = some (after, handle) ∧
      next = (fun owner => if owner = view.owner then some after else storage owner) := by
  unfold View.expose at step
  cases found : storage view.owner with
  | none => simp [found] at step
  | some before =>
      simp only [found] at step
      split at step
      · rename_i owned
        cases exposed : SourcePreparation.expose before index with
        | none => simp [exposed] at step
        | some result =>
            rcases result with ⟨after, ticket⟩
            simp only [exposed, Option.some.injEq, Prod.mk.injEq] at step
            rcases step with ⟨sameStorage, sameHandle⟩
            subst ticket
            exact ⟨before, after, rfl, owned, exposed, sameStorage.symm⟩
      · simp_all

/-- Reflecting through either alias fences new capture through BOTH views.
It does not revoke the immutable recipes held by an already prepared receiver. -/
theorem View.exposure_revokes_alias_issuance {Self Value : Type}
    (storage next : Storage Self Value) (view alias : View) (index : Nat) (handle : Handle)
    (sameOwner : alias.owner = view.owner)
    (step : View.expose storage view index = some (next, handle)) :
    View.issue next alias = none := by
  rcases View.exposure_witness _ _ _ _ _ step with
    ⟨before, after, _found, owned, exposed, rfl⟩
  have currentOwner : after.identity = view.owner :=
    (exposure_keeps_producer_snapshot _ _ _ _ exposed).2.trans owned
  simp [View.issue, sameOwner, currentOwner, exposure_revokes_new_issuance _ _ _ _ exposed]

/-- The update touches one registered storage owner; unrelated storage/views
retain their exact issuance result without enumerating the other owners. -/
theorem View.exposure_other_owner_frame {Self Value : Type}
    (storage next : Storage Self Value) (view other : View) (index : Nat) (handle : Handle)
    (separate : other.owner ≠ view.owner)
    (step : View.expose storage view index = some (next, handle)) :
    View.issue next other = View.issue storage other := by
  rcases View.exposure_witness _ _ _ _ _ step with
    ⟨_before, _after, _found, _owned, _exposed, rfl⟩
  simp only [View.issue, separate, ↓reduceIte]

namespace ThunkRows

def assign {Key Value : Type} [DecidableEq Key]
    (before : Key → CapturedBinding.Target Value) (row : Key × (Unit → Value)) :
    Key → CapturedBinding.Target Value :=
  fun key => if key = row.1 then .procedure row.2 else before key

def install {Key Value : Type} [DecidableEq Key]
    (rows : List (Key × (Unit → Value))) (before : Key → CapturedBinding.Target Value) :
    Key → CapturedBinding.Target Value :=
  match rows with
  | [] => before
  | row :: rest => install rest (assign before row)

/-- Ordinary chronological independent-thunk binding after complete generated
source admission. This does not model an unknown/raw SlotSpec admission skip. -/
def compile {Key Self Value : Type} [DecidableEq Key] (receiver : Self) (key : Key)
    (rows : List (Key × (Unit → Value))) (before : CapturedBinding.Target Value) :
    CapturedBinding.Target Value :=
  match rows with
  | [] => before
  | row :: rest => compile receiver key rest
      (if key = row.1 then CapturedBinding.bind receiver (.thunk (.procedure row.2)) before else before)

theorem install_equals_compile {Key Self Value : Type} [DecidableEq Key]
    (receiver : Self) (key : Key) (rows : List (Key × (Unit → Value)))
    (before : Key → CapturedBinding.Target Value) :
    install rows before key = compile receiver key rows (before key) := by
  induction rows generalizing before with
  | nil => rfl
  | cons row rest ih =>
    simp only [install, compile, ih, assign, CapturedBinding.bind]

/-- Duplicate names keep the newest actual function, and names not installed
retain the original missing-method target. No thunk body is invoked. -/
theorem duplicate_and_absent_control :
    let before : Nat → CapturedBinding.Target Nat := fun _ => .nonCallable
    let first : Unit → Nat := fun _ => 7
    let last : Unit → Nat := fun _ => 11
    install [(0, first), (0, last)] before 0 = .procedure last ∧
      install [(0, first), (0, last)] before 1 = .nonCallable := by
  simp [install, assign]

end ThunkRows

namespace RecipeRows

/-- Chronological source contributions bind the final receiver. The index is
the existing method dictionary; no computed business result is installed here. -/
def assign {Key Self Value : Type} [DecidableEq Key] (receiver : Self)
    (before : Key → CapturedBinding.Target Value) (row : Key × Recipe Self Value) :
    Key → CapturedBinding.Target Value :=
  fun key => if key = row.1 then
    CapturedBinding.bind receiver row.2.capture (before key) else before key

def install {Key Self Value : Type} [DecidableEq Key] (receiver : Self) :
    List (Key × Recipe Self Value) →
      (Key → CapturedBinding.Target Value) → Key → CapturedBinding.Target Value
  | [], before => before
  | row :: rest, before => install receiver rest (assign receiver before row)

/-- Reference per-key binding in the same contribution order. C4 establishes
this schedule before either interpretation; it is not inferred from a tree. -/
def compile {Key Self Value : Type} [DecidableEq Key] (receiver : Self) (key : Key) :
    List (Key × Recipe Self Value) → CapturedBinding.Target Value → CapturedBinding.Target Value
  | [], before => before
  | row :: rest, before => compile receiver key rest
      (if key = row.1 then CapturedBinding.bind receiver row.2.capture before else before)

theorem install_equals_compile {Key Self Value : Type} [DecidableEq Key]
    (receiver : Self) (key : Key) (rows : List (Key × Recipe Self Value))
    (before : Key → CapturedBinding.Target Value) :
    install receiver rows before key = compile receiver key rows (before key) := by
  induction rows generalizing before with
  | nil => rfl
  | cons row rest ih =>
    simp only [install, compile, ih, assign]

/-- The ordinary generated self form captures its actual function and final
receiver without evaluating that function or inspecting an inherited value. -/
theorem self_binds_final_receiver {Key Self Value : Type} [DecidableEq Key]
    (receiver : Self) (key : Key) (body : Self → Value)
    (before : Key → CapturedBinding.Target Value) :
    install receiver [(key, .self body)] before key =
      .procedure (fun _ => body receiver) := by
  simp [install, assign, Recipe.capture, CapturedBinding.bind]

/-- Computed contributions retain the exact inherited target; even a missing
parent remains delayed. This does not authorize skipping earlier tag admission. -/
theorem computed_keeps_delayed_parent {Key Self Value : Type} [DecidableEq Key]
    (receiver : Self) (key : Key)
    (body : Self → CapturedBinding.Target Value → Value)
    (before : Key → CapturedBinding.Target Value) :
    install receiver [(key, .computed body)] before key =
      .procedure (fun _ => body receiver (before key)) := by
  simp [install, assign, Recipe.capture, CapturedBinding.bind]

theorem unrelated_key_unchanged {Key Self Value : Type} [DecidableEq Key]
    (receiver : Self) (key other : Key) (different : key ≠ other)
    (body : Recipe Self Value) (before : Key → CapturedBinding.Target Value) :
    install receiver [(other, body)] before key = before key := by
  simp [install, assign, different]

/-- Source reuse does not reuse a receiver-bound method. Two mounts of one
recipe still bind their own final self, while duplicate keys keep the last
super-independent contribution. No source body is run during installation. -/
theorem final_receiver_and_duplicate_control :
    let before : Nat → CapturedBinding.Target Nat := fun _ => .nonCallable
    let rows : List (Nat × Recipe Nat Nat) :=
      [(0, .self (fun self => self + 1)), (0, .self (fun self => self + 7))]
    install 3 rows before 0 = .procedure (fun _ => 10) ∧
      install 5 rows before 0 = .procedure (fun _ => 12) ∧
      install 3 rows before 1 = .nonCallable := by
  simp [install, assign, Recipe.capture, CapturedBinding.bind]

/-- A newer raw prefix can end in an already captured inherited method.
This is still the original binding kernel, not a second method evaluator. -/
def newest {Self Value : Type} (receiver : Self) :
    List (CapturedBinding.Spec Self Value) → CapturedBinding.Target Value →
      CapturedBinding.Target Value
  | [], inherited => inherited
  | spec :: rest, inherited => CapturedBinding.bind receiver spec (newest receiver rest inherited)

theorem newest_equals_original {Self Value : Type} (receiver : Self)
    (specs : List (CapturedBinding.Spec Self Value)) (inherited : CapturedBinding.Target Value) :
    newest receiver specs inherited = CapturedBinding.bindChain receiver specs.reverse inherited := by
  induction specs with
  | nil => rfl
  | cons spec rest ih =>
    simp only [newest, ih, CapturedBinding.bindChain, List.reverse_cons,
      List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Sharing a captured tail preserves the full contribution order, including
several computed modifiers above it. Final receiver remains an explicit input. -/
theorem newest_append {Self Value : Type} (receiver : Self)
    (outer inner : List (CapturedBinding.Spec Self Value)) (inherited : CapturedBinding.Target Value) :
    newest receiver (outer ++ inner) inherited =
      newest receiver outer (newest receiver inner inherited) := by
  induction outer with
  | nil => rfl
  | cons spec rest ih => simp only [List.cons_append, newest, ih]

def independent {Self Value : Type} : Recipe Self Value → Prop
  | .constant _ | .thunk _ | .self _ => True
  | .computed _ => False

/-- Only a generated independent contribution may replace its older chain
with a bound method. Ordinary raw tag admission still precedes this operation. -/
theorem independent_discards_tail {Self Value : Type} (receiver : Self)
    (recipe : Recipe Self Value) (supported : independent recipe)
    (left right : CapturedBinding.Target Value) :
    CapturedBinding.bind receiver recipe.capture left =
      CapturedBinding.bind receiver recipe.capture right := by
  cases recipe <;> simp_all [independent, Recipe.capture, CapturedBinding.bind]

end RecipeRows
end LeanPoo.Object.SourcePreparation
