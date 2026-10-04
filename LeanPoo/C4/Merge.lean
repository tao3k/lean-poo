import Std
import LeanPoo.C4.Types

/-!
Ordered candidate merging translated from François-René Rideau's C4-Mixins,
include/c4/linearize.hpp.
Upstream offers Apache-2.0 or No Problem Bugroff; this translation uses Apache-2.0.
-/

namespace LeanPoo.C4

/- The named state operations are exposed for the kernel simulation proof.
The runtime merger retains its incremental hash-map algorithm. -/
namespace MergeState

abbrev Counts := Std.HashMap String Nat

@[inline] def increment (counts : Counts) (name : String) : Counts :=
  counts.insert name (counts.getD name 0 + 1)

@[inline] def decrement (counts : Counts) (name : String) : Counts :=
  counts.insert name (counts.getD name 0 - 1)

/-- C4-Mixins counts candidates appearing in a list tail. -/
def ancestorCounts (lists : List (List String)) : Counts :=
  lists.foldl (fun counts list =>
    (list.drop 1).foldl increment counts) {}

/-- The first head with no remaining appearance in a candidate tail. -/
def eligibleHead? (lists : List (List String)) (counts : Counts) : Option String :=
  (lists.filterMap List.head?).find? (fun head => counts.getD head 0 == 0)

@[inline] def consume (next : String) (state : List (List String) × List String)
    (list : List String) : List (List String) × List String :=
  let (reversed, newHeads) := state
  match list with
  | head :: tail =>
    if head == next then
      let newHeads := match tail with
        | [] => newHeads
        | newHead :: _ => newHead :: newHeads
      (tail :: reversed, newHeads)
    else (list :: reversed, newHeads)
  | [] => (reversed, newHeads)

def mergeStep (result : List String) (lists : List (List String))
    (counts : Counts) : Except Error (List String × List (List String) × Counts) := do
  let pending := lists.filter (fun list => !list.isEmpty)
  if pending.isEmpty then
    return (result, pending, counts)
  let some next := eligibleHead? pending counts | throw .inconsistentOrder
  let (reversed, newHeads) := pending.foldl (consume next) ([], [])
  let updatedCounts := newHeads.foldl decrement counts
  return (next :: result, reversed.reverse.filter (fun list => !list.isEmpty), updatedCounts)

@[inline] def round (state : Except Error (List String × List (List String) × Counts))
    (_ : Nat) : Except Error (List String × List (List String) × Counts) := do
  let (result, pending, counts) ← state
  mergeStep result pending counts

end MergeState

/-- C3's ordered merge with C4-Mixins' incremental tail counts.
Each successful step removes at least one candidate, so the sum of candidate
lengths is a sufficient finite bound. -/
def merge (lists : List (List String)) : Except Error (List String) := do
  let steps := lists.foldl (fun count list => count + list.length) 0
  let initial : Except Error (List String × List (List String) × MergeState.Counts) :=
    .ok ([], lists, MergeState.ancestorCounts lists)
  let final := (List.range steps).foldl MergeState.round initial
  let (result, pending, _) ← final
  if pending.all List.isEmpty then
    return result.reverse
  throw .inconsistentOrder

end LeanPoo.C4
