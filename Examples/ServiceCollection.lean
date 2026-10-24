import LeanPoo.Functional.CacheLookup
import LeanPoo.Functional.TableFold

/-! Ordered host Iterable observations over source-bound recursive service rows.
The host hash/interface and iterator laws are premises; no GC/dispatch proof is asserted.
-/
namespace Examples.ServiceCollection
open LeanPoo.Functional
open LeanPoo.Functional.ConstructionCache

/-- The two alternatives distinguish stored false from a missing table entry. -/
def values : Nat → Option (Option Bool) := fun key => if key = 0 then some (some false) else some none
example : lookupOr (values 0) (fun _ => Except.error "unexpected fallback") = .ok (some false) := rfl
example : lookupOr (values 1) (fun _ => Except.error "unexpected fallback") = .ok none := rfl

/-- A symbolic shape identity stands for the exact live object held by layouts. -/
def shapes : Nat → Option Nat := fun _ => none
example : ensureLookup shapes 0 (fun _ => Except.error "constructor failure") =
    (.error "constructor failure", shapes) := rfl
example : ensureLookup (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2
    0 (fun _ => Except.error "must not rebuild") =
      (.ok 7, (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2) :=
  ensureLookup_repeat shapes 0 7 _ _ rfl rfl

/-- Iterator pulls retain order; a wrapping refusal stops before later service rows. -/
def wrap (row : Nat) : Except String Nat := if row = 2 then .error "invalid method" else .ok (row + 10)
example : Validation.traverse wrap [0, 1] = .ok [10, 11] := rfl
example : Validation.traverse wrap [0, 2, 1] = .error "invalid method" := rfl
/-- The diagnostic builder preserves issue order and multiplicity. -/
example : Validation.gatherIssues (fun (row : Nat) => [row, row + 10]) [0, 1] = [0, 10, 1, 11] := rfl

/-- Row admission delegates the guard before wrapping and observing through FUN. -/
example : Validation.checkThen (fun (_ : Nat) => Except.ok false) "shape"
    wrap (fun _ => Except.error "consumer must not run" : Nat → Except String Nat) 2 =
      .error "shape" := rfl

open LeanPoo.Functional.OrderedDictionary

/-- Team/capacity rows model the numeric observation of Function-bearing services;
opaque callbacks remain in host rows and are never reconstructed by aggregation. -/
def capacityBefore (key : Nat) : Option (Nat × Int) :=
  match key with
  | 1 => some (10, 5)
  | 2 => some (10, -5)
  | 9 => some (90, 4)
  | _ => none

/-- A service migrates while an unrelated team's complete bucket is unchanged. -/
def capacityAfter (key : Nat) : Option (Nat × Int) :=
  if key = 1 then some (20, 7) else capacityBefore key

/-- The reference sum uses one fixed, complete finite inventory. -/
def teamCapacity (groups : Nat → Nat → Option (Nat × Int)) (team : Nat) : Option Int :=
  foldGroups [1, 2, 9] (foldView [1, 2, 9] (fun _ row => row.2)) groups team

/-- A present zero aggregate is distinct from no group; missing team 20 is absent. -/
example : [10, 20, 90].map (teamCapacity (indexView (fun _ row => row.1) capacityBefore)) =
    [some 0, none, some 4] := rfl

/-- Old and new group repair retains team 90 and publishes the migration exactly. -/
example : [10, 20, 90].map (repairGroupFolds [10, 20]
    (teamCapacity (indexView (fun _ row => row.1) capacityAfter))
    (teamCapacity (indexView (fun _ row => row.1) capacityBefore))) =
    [some (-5), some 7, some 4] := rfl

/-- Removing both owners erases the zero-sum group instead of retaining a ghost 0. -/
example : teamCapacity (indexView (fun _ row => row.1)
    (replace (replace capacityBefore 1 none) 2 none)) 10 = none := rfl

/-- Ordered source inverses recover the original zero-valued group and every
other aggregate, without assuming the sum is an invertible representation. -/
example (edits : List (Change Nat (Nat × Int)))
    (ready : applyChanges edits capacityBefore = .ok capacityAfter) :
    (applyChanges (inverseChanges edits) capacityAfter).map
      (fun restored => teamCapacity (indexView (fun _ row => row.1) restored)) =
      .ok (teamCapacity (indexView (fun _ row => row.1) capacityBefore)) := by
  rw [applyChanges_inverse edits capacityBefore capacityAfter ready]
  rfl
end Examples.ServiceCollection
