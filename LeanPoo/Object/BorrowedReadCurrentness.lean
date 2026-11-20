-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.BorrowedReadCurrentness

/-- Native shape indices select cells; none denotes the actual missing sentinel. -/
structure Store where
  indices : Nat → Option Nat
  cells : Nat → Option Nat

def Store.lookup (store : Store) (key : Nat) : Option Nat :=
  (store.indices key).bind store.cells

structure Receiver where
  revision : Nat
  storageId : Nat
  store : Store
  reads : Nat → Option Nat
  anchors : Nat → Option Nat

inductive Kind where
  | bootstrap | cacheMiss | structural | value
  deriving DecidableEq, Repr

structure Read where
  identity : Nat
  revision : Nat
  storageId : Nat
  key : Nat
  value : Option Nat
  kind : Kind
  deriving DecidableEq, Repr

/-- Public HashTable operations, after native route admission. -/
def ordinary (receiver : Receiver) (read : Read) : Bool :=
  read.revision == receiver.revision &&
  match read.kind with
  | .bootstrap => match receiver.anchors read.key with
      | none => false
      | some value => some value == read.value
  | .cacheMiss => read.storageId == receiver.storageId &&
      (receiver.store.lookup read.key).isNone
  | .structural => read.storageId == receiver.storageId &&
      receiver.reads read.key == some read.identity
  | .value => read.storageId == receiver.storageId &&
      receiver.reads read.key == some read.identity &&
      receiver.store.lookup read.key == read.value

/-- A view borrows the already admitted native fields in this sweep only.
It is not a retained authentication result. -/
structure View where
  revision : Nat
  storageId : Nat
  reads : Nat → Option Nat
  indices : Nat → Option Nat
  cells : Nat → Option Nat

def borrow (receiver : Receiver) : View :=
  ⟨receiver.revision, receiver.storageId, receiver.reads,
    receiver.store.indices, receiver.store.cells⟩

def nativeLookup (view : View) (key : Nat) : Option Nat :=
  match view.indices key with
  | none => none
  | some index => view.cells index

def vectorCurrent (view : View) (read : Read) : Bool :=
  read.revision == view.revision &&
  read.storageId == view.storageId &&
  match read.kind with
  | .cacheMiss => (nativeLookup view read.key).isNone
  | .structural => view.reads read.key == some read.identity
  | .value => view.reads read.key == some read.identity &&
      nativeLookup view read.key == read.value
  | .bootstrap => false

/-- Bootstrap reads never consume or establish a vector route. -/
def borrowed (live : Receiver) (view : View) (read : Read) : Bool :=
  if read.kind = .bootstrap then ordinary live read else vectorCurrent view read

theorem native_lookup_exact (receiver : Receiver) (key : Nat) :
    nativeLookup (borrow receiver) key = receiver.store.lookup key := by
  cases present : receiver.store.indices key <;>
    simp [nativeLookup, borrow, Store.lookup, present, Option.bind]

theorem same_window_exact (receiver : Receiver) (read : Read) :
    borrowed receiver (borrow receiver) read = ordinary receiver read := by
  cases kind : read.kind <;>
    simp only [borrowed, vectorCurrent, ordinary, kind, nativeLookup, borrow,
      Store.lookup, Bool.and_assoc, ite_true, ite_false, reduceCtorEq]
  all_goals cases receiver.store.indices read.key <;> rfl

/-- No callback, source guard or foreign delegate may occur while borrowing.
A changed storageId/epoch, cell, index or read-table membership needs a fresh view.
Anchors remain live because bootstrap takes the ordinary path. -/
def SameNativeWindow (before after : Receiver) : Prop :=
  before.revision = after.revision ∧ before.storageId = after.storageId ∧
  before.reads = after.reads ∧ before.store.indices = after.store.indices ∧
  before.store.cells = after.store.cells

theorem borrow_eq (before after : Receiver) (stable : SameNativeWindow before after) :
    borrow before = borrow after := by
  rcases stable with ⟨revision, storageId, reads, indices, cells⟩
  simp [borrow, revision, storageId, reads, indices, cells]

theorem interval_exact (before after : Receiver) (stable : SameNativeWindow before after)
    (read : Read) :
    borrowed after (borrow before) read = ordinary after read := by
  rw [borrow_eq before after stable, same_window_exact]

/-- Issue, key and route checks keep their original order and first failure.
Only the final native Slot-state implementation is substituted. -/
def sweep (guards : Read → Except Nat Unit) (live : Read → Bool) :
    List Read → Except Nat Unit
  | [] => .ok ()
  | read :: rest => do
    guards read
    if live read then sweep guards live rest else .error 3

theorem sweep_exact (receiver : Receiver) (guards : Read → Except Nat Unit)
    (reads : List Read) :
    sweep guards (borrowed receiver (borrow receiver)) reads =
      sweep guards (ordinary receiver) reads := by
  have same : borrowed receiver (borrow receiver) = ordinary receiver :=
    funext (same_window_exact receiver)
  rw [same]

theorem independent_return (before after : Receiver)
    (guardsBefore guardsAfter : Read → Except Nat Unit) (reads : List Read) :
    (sweep guardsBefore (borrowed before (borrow before)) reads >>= fun _ =>
      sweep guardsAfter (borrowed after (borrow after)) reads) =
    (sweep guardsBefore (ordinary before) reads >>= fun _ =>
      sweep guardsAfter (ordinary after) reads) := by
  rw [sweep_exact, sweep_exact]

private def empty : Receiver :=
  ⟨0, 1, ⟨fun _ => none, fun _ => none⟩, fun _ => none, fun _ => none⟩
private def missing : Read := ⟨2, 0, 1, 4, none, .cacheMiss⟩
private def filled : Receiver :=
  { empty with store := ⟨fun _ => some 0, fun _ => some 9⟩ }

/-- Cache population can change a missing result without advancing revision.
Keeping an earlier borrowed route across a callback would wrongly accept it. -/
example : vectorCurrent (borrow empty) missing = true ∧
    ordinary filled missing = false := by constructor <;> rfl

example : sweep (fun _ => .error 7) (ordinary empty) [missing] = .error 7 := rfl

end LeanPoo.Object.BorrowedReadCurrentness
