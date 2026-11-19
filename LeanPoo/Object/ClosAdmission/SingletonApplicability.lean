-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission

namespace LeanPoo.Object.ClosAdmission.SingletonApplicability

open IndexedRank (Attempt)

variable {Row Rank State Error Event : Type}

abbrev Result (A : Type) (State Error Event : Type) := Except Error A × State × List Event

def collect (step : Row → Attempt State Error Event Rank) :
    List Row → State → Result (List (Option Rank)) State Error Event
  | [], state => (.ok [], state, [])
  | row :: rows, state =>
    match step row state with
    | (.error refusal, after, reads) => (.error refusal, after, reads)
    | (.ok distance, after, reads) =>
      let (rest, final, later) := collect step rows after
      (rest.map (distance :: ·), final, reads ++ later)

/-- Visit the next row even when a previous row was a miss. The flag only
    summarizes results. Every read or refusal comes from the original step. -/
def check (step : Row → Attempt State Error Event Rank) :
    List Row → State → Bool → Result Bool State Error Event
  | [], state, applicable => (.ok applicable, state, [])
  | row :: rows, state, applicable =>
    match step row state with
    | (.error refusal, after, reads) => (.error refusal, after, reads)
    | (.ok distance, after, reads) =>
      let (rest, final, later) := check step rows after (applicable && distance.isSome)
      (rest, final, reads ++ later)

theorem one_pass_preserves_applicability (step : Row → Attempt State Error Event Rank)
    (rows : List Row) (state : State) (applicable : Bool) :
    check step rows state applicable =
      let (outcome, after, reads) := collect step rows state
      (outcome.map (fun values => applicable && values.all Option.isSome), after, reads) := by
  induction rows generalizing state applicable with
  | nil => simp [check, collect, Except.map]
  | cons row rows ih =>
    cases h : step row state with
    | mk outcome tail =>
      rcases tail with ⟨after, reads⟩
      cases outcome with
      | error refusal => simp [check, collect, h, Except.map]
      | ok result =>
        simp only [check, collect, h, ih]
        cases collect step rows after with
        | mk rest tail =>
          rcases tail with ⟨final, later⟩
          cases rest <;> simp [Except.map, Bool.and_assoc]

def ordering (read : State → Result Unit State Error Event)
    (selection : Result Bool State Error Event) : Result Bool State Error Event :=
  match selection with
  | (.error refusal, after, reads) => (.error refusal, after, reads)
  | (.ok applicable, after, reads) =>
    let (outcome, final, later) := read after
    (outcome.map (fun _ => applicable), final, reads ++ later)

/-- An applicable zero (including eql) is present. The ordering read runs
    after the entire scan even on a miss, and never hides a prior refusal. -/
theorem singleton_keeps_first_refusal_and_ordering_read
    (step : Row → Attempt State Error Event Rank) (read : State → Result Unit State Error Event)
    (rows : List Row) (state : State) :
    ordering read (check step rows state true) = ordering read
      (let (outcome, after, reads) := collect step rows state
       (outcome.map (List.all · Option.isSome), after, reads)) := by
  simpa using congrArg (ordering read) (one_pass_preserves_applicability step rows state true)

/-- Applicability keeps at most one method here. The array and comparator
    serve only the multi-method ordering. Consumers of the singleton use the
    method identity, including reflection, combination and next-method checks. -/
def singletonRanked (method : Method) (ranks : List (Option Rank)) :
    List (Method × Array Rank) :=
  if ranks.all Option.isSome then [(method, (ranks.filterMap id).toArray)] else []

theorem singleton_sort_and_array_erase
    (method : Method) (ranks : List (Option Rank))
    (precedes : Method × Array Rank → Method × Array Rank → Bool) :
    ((singletonRanked method ranks).mergeSort precedes).map Prod.fst =
      (if ranks.all Option.isSome then [method] else []) := by
  cases selected : ranks.all Option.isSome <;> simp [singletonRanked, selected]

theorem singleton_consumers_get_same_method
    (step : Row → Attempt State Error Event Rank) (rows : List Row) (state : State)
    (method : Method) (precedes : Method × Array Rank → Method × Array Rank → Bool) :
    (let (outcome, after, events) := check step rows state true
     (outcome.map (fun applicable => if applicable then [method] else []), after, events)) =
    (let (outcome, after, events) := collect step rows state
     (outcome.map (fun ranks => ((singletonRanked method ranks).mergeSort precedes).map Prod.fst),
      after, events)) := by
  rw [one_pass_preserves_applicability]
  rcases collect step rows state with ⟨outcome, after, events⟩
  cases outcome <;> simp [Except.map, singleton_sort_and_array_erase]

end LeanPoo.Object.ClosAdmission.SingletonApplicability
