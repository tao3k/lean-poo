-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ReverseIndexTraversal

abbrev Action (World Failure : Type) := ExceptT Failure (StateM World)

inductive Step (Key Edge Cursor : Type) where
  | done
  | entry (key : Key) (edge : Edge) (remaining : Cursor)

abbrev CursorRead (World Failure Key Edge Cursor : Type) :=
  Cursor → Action World Failure (Step Key Edge Cursor)

/-- The iterator yields a pair, then resumes the same HashTable producer.
The next row can depend on effects left by the previous visit. -/
def iteratorVisit (visit : Key → Edge → Action World Failure Unit)
    (event : Key × Edge) : Action World Failure Unit :=
  let (key, edge) := event
  visit key edge

def enumerate (next : CursorRead World Failure Key Edge Cursor)
    (visit : Key → Edge → Action World Failure Unit) :
    Nat → Cursor → Action World Failure Unit
  | 0, _ => pure ()
  | steps + 1, cursor => do
    match ← next cursor with
    | .done => pure ()
    | .entry key edge remaining =>
      visit key edge
      enumerate next visit steps remaining

/-- Direct enumeration passes the two fields to the same visit. Skipped
edges, descendant recursion and refusal can all be effects of that visit. -/
theorem enumerate_without_pair_adapter
    (next : CursorRead World Failure Key Edge Cursor)
    (visit : Key → Edge → Action World Failure Unit) (steps : Nat) (cursor : Cursor) :
    enumerate next (fun key edge => iteratorVisit visit (key, edge)) steps cursor =
    enumerate next visit steps cursor := by
  rfl

/-- The last graph certification sees the world left by all visits,
including edges registered by preflight. A refusal reaches neither clear
nor assignment. -/
def commit (prepare certify clear assign : Action World Failure Unit) :
    Action World Failure Unit := do
  prepare
  certify
  clear
  assign

theorem commit_without_pair_adapter
    (next : CursorRead World Failure Key Edge Cursor)
    (visit : Key → Edge → Action World Failure Unit) (steps : Nat) (cursor : Cursor)
    (certify clear assign : Action World Failure Unit) :
    commit (enumerate next (fun key edge => iteratorVisit visit (key, edge)) steps cursor)
      certify clear assign =
    commit (enumerate next visit steps cursor) certify clear assign := by
  rw [enumerate_without_pair_adapter]

end LeanPoo.Object.ReverseIndexTraversal
