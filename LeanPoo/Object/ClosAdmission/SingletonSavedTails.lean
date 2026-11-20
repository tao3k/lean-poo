-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.SingletonApplicability

namespace LeanPoo.Object.ClosAdmission.SingletonSavedTails

open IndexedRank (Attempt)
open SingletonApplicability (check collect ordering singleton_keeps_first_refusal_and_ordering_read)

inductive Position where
  | specializers
  | arguments
  deriving DecidableEq

inductive ListRefusal where
  | list (position : Position)
  | properList (position : Position)
  | length (position : Position)
  deriving DecidableEq

inductive Cell (Head Cursor : Type) where
  | pair (head : Head) (tail : Cursor)
  | end
  | improper

inductive Probe (Left Right L R : Type) where
  | row (left : Left) (right : Right) (nextLeft : L) (nextRight : R)
  | done
  | refused (cause : ListRefusal)

variable {Left Right L R State Error Event Rank : Type}

private def invalid (initial : Bool) (position : Position) : ListRefusal :=
  if initial then .list position else .properList position

/-- Two-list Gambit map rejects an improper cursor before testing for a length
    mismatch. For two improper cursors the first argument's refusal wins. -/
def probe (initial allowMismatch : Bool) (left : Cell Left L) (right : Cell Right R) :
    Probe Left Right L R :=
  match left, right with
  | .improper, _ => .refused (invalid initial .specializers)
  | _, .improper => .refused (invalid initial .arguments)
  | .pair l lt, .pair r rt => .row l r lt rt
  | .end, .end => .done
  | .end, .pair .. => if allowMismatch then .done else .refused (.length .specializers)
  | .pair .., .end => if allowMismatch then .done else .refused (.length .arguments)

/-- The native two-list cdrs builds the right tail list before extending it
    with the left tail. A malformed left cursor overrides the right result. -/
private def libraryTails (initial allowMismatch : Bool)
    (left : Cell Left L) (right : Cell Right R) : Except ListRefusal (List (Sum L R)) :=
  let rightTails : Except ListRefusal (List (Sum L R)) :=
    match right with
    | .improper => .error (invalid initial .arguments)
    | .end => .ok []
    | .pair _ tail => .ok [Sum.inr tail]
  match left with
  | .improper => .error (invalid initial .specializers)
  | .end =>
    rightTails.bind (fun
      | [] => .ok []
      | _ :: _ => if allowMismatch then .ok [] else .error (.length .specializers))
  | .pair _ tail =>
    rightTails.bind (fun
      | [] => if allowMismatch then .ok [] else .error (.length .arguments)
      | tails@(_ :: _) => .ok (.inl tail :: tails))

private def libraryProbe (initial allowMismatch : Bool)
    (left : Cell Left L) (right : Cell Right R) : Probe Left Right L R :=
  match libraryTails initial allowMismatch left right, left, right with
  | .error cause, _, _ => .refused cause
  | .ok [.inl lt, .inr rt], .pair l _, .pair r _ => .row l r lt rt
  | _, _, _ => .done

private theorem probe_erases_library_tail_pairs :
    @probe Left Right L R = libraryProbe := by
  funext initial allowMismatch left right
  cases left <;> cases right <;> cases allowMismatch <;>
    simp [probe, libraryProbe, libraryTails, Except.bind]

abbrev TraversalState (L R State : Type) := Option (L × R) × Bool × State

/-- Snapshot both cursor tails in the pre-read state. The callback can
    replace a cdr, but the next iteration starts at the original pointers
    and inspects what those cells contain in the updated state. -/
private def advanceWith
    (inspect : Bool → Bool → Cell Left L → Cell Right R → Probe Left Right L R)
    (left : L → State → Cell Left L) (right : R → State → Cell Right R)
    (allowMismatch : State → Bool) (read : Left → Right → Attempt State Error Event Rank)
    (neutral : Rank) (_ : Unit) :
    Attempt (TraversalState L R State) (Sum ListRefusal Error) Event Rank :=
  fun (cursors, initial, state) =>
    match cursors with
    | none => (.ok (some neutral), (none, initial, state), [])
    | some (l, r) =>
      match inspect initial (allowMismatch state) (left l state) (right r state) with
      | .done => (.ok (some neutral), (none, initial, state), [])
      | .refused cause => (.error (.inl cause), (none, initial, state), [])
      | .row lHead rHead lTail rTail =>
        match read lHead rHead state with
        | (.error refusal, after, events) => (.error (.inr refusal), (none, false, after), events)
        | (.ok result, after, events) => (.ok result, (some (lTail, rTail), false, after), events)

private abbrev advance := @advanceWith Left Right L R State Error Event Rank probe

/-- The Scheme loop needs only two next pointers and a Boolean. It executes
    the same probes and effects as collecting the distances before reducing
    them. The ordering slot is read after a normal scan, including a miss. -/
theorem saved_tails_preserve_selection
    (left : L → State → Cell Left L) (right : R → State → Cell Right R)
    (allowMismatch : State → Bool) (read : Left → Right → Attempt State Error Event Rank)
    (neutral : Rank) (budget : List Unit) (cursor : TraversalState L R State)
    (readOrder : TraversalState L R State →
      SingletonApplicability.Result Unit (TraversalState L R State) (Sum ListRefusal Error) Event) :
    ordering readOrder (check (advance left right allowMismatch read neutral) budget cursor true) =
      ordering readOrder
        (let (result, after, events) :=
          collect (advanceWith libraryProbe left right allowMismatch read neutral) budget cursor
         (result.map (List.all · Option.isSome), after, events)) := by
  rw [← probe_erases_library_tail_pairs]
  exact singleton_keeps_first_refusal_and_ordering_read
    (advance left right allowMismatch read neutral) readOrder budget cursor

private def specializers (cursor : Nat) (_ : Bool) : Cell Nat Nat :=
  if cursor < 2 then .pair cursor (cursor + 1) else .end

private def arguments (cursor : Nat) (rewired : Bool) : Cell Unit Nat :=
  if cursor == 0 then .pair () (if rewired then 3 else 1)
  else if cursor < 3 then .pair () (cursor + 1)
  else .end

private def readSpecializer (position : Nat) (_ : Unit) : Attempt Bool Unit Nat Unit :=
  fun rewired =>
    if position == 0 then (.ok none, true, [position])
    else (.error (), rewired, [position])

/-- A miss that rewires the argument spine cannot suppress a later refusal. -/
example :
    let (result, _, reads) := check
      (advance specializers arguments (fun _ => true) readSpecializer ())
      [(), (), ()] (some (0, 0), true, false) true
    result = .error (.inr ()) ∧ reads = [0, 1] := by constructor <;> rfl

example :
    probe false false (.end : Cell Unit Unit) (.improper : Cell Unit Unit) =
      .refused (.properList .arguments) := rfl

example :
    probe true false (.improper : Cell Unit Unit) (.improper : Cell Unit Unit) =
      .refused (.list .specializers) := rfl

end LeanPoo.Object.ClosAdmission.SingletonSavedTails
