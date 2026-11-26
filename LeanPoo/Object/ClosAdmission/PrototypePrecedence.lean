-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosAdmission.PrototypePrecedence

variable {Prototype State Failure Event Result : Type}

abbrev Preparation (Prototype State Failure Event : Type) :=
  State → Except Failure (List Prototype) × State × List Event

-- The public MOP query copies the list spine while retaining prototype identity.
def snapshot (order : List Prototype) : List Prototype := order.map id

-- Stock warm queries return the admitted order. Cold preparation includes
-- C4, author hooks, and their refusal and read traces.
def query (warm : Option (List Prototype)) (prepare : Preparation Prototype State Failure Event)
    (project : List Prototype → Result) (state : State) :
    Except Failure Result × State × List Event :=
  match warm with
  | some order => (.ok (project order), state, [])
  | none =>
    let (result, after, reads) := prepare state
    (result.map project, after, reads)

def position [DecidableEq Prototype] (target : Prototype) (order : List Prototype) : Option Nat :=
  let tail := order.dropWhile (fun current => decide (current ≠ target))
  if tail.isEmpty then none else some (order.length - tail.length)

/-- A scalar query can use the canonical list immediately after preparation.
    The public snapshot remains necessary for callers that retain the list
    or cross an open callback with it. -/
theorem reads_and_refusal_unchanged (warm : Option (List Prototype))
    (prepare : Preparation Prototype State Failure Event)
    (project : List Prototype → Result) (state : State) :
    query warm prepare project state =
      match warm with
      | some order => (.ok (project order), state, [])
      | none => query none prepare (project ∘ snapshot) state := by
  have same : project ∘ snapshot = project := by
    funext order
    simp [snapshot]
  rw [same]
  cases warm <;> rfl

theorem positions_and_depth_unchanged [DecidableEq Prototype]
    (warm : Option (List Prototype)) (prepare : Preparation Prototype State Failure Event)
    (target : Prototype) (state : State) :
    query warm prepare (fun order => (position target order, order.length)) state =
      match warm with
      | some order => (.ok (position target order, order.length), state, [])
      | none =>
        query none prepare (fun order => (position target (snapshot order),
          (snapshot order).length)) state :=
  reads_and_refusal_unchanged warm prepare _ state

#print axioms positions_and_depth_unchanged

end LeanPoo.Object.ClosAdmission.PrototypePrecedence
