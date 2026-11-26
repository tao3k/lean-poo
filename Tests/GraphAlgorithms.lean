import LeanPoo.Functional.OrderedReachability
import LeanPoo.Functional.StableOrderRepair
import LeanPoo.Functional.ComponentWitness

open LeanPoo.Functional.DependencyOrderRepair

-- Sparse labels are assigned to exactly the same owner identities.
#guard (proposeRanks id [1, 2] [2, 3]).isNone
#guard (proposeRanks (fun _ => 0) [1] [2]).isNone
#guard repairRanks id [9998] [1] 9998 == 1
#guard repairRanks id [9998] [1] 1 == 9998
#guard (List.range 10000).all (fun node =>
  repairRanks id [9998] [1] node ==
    (if node = 1 then 9998 else if node = 9998 then 1 else node))

-- An inverted rank is not evidence of a cycle.
example : ¬ Cycle (inserted (fun _ _ : Fin 2 => false) 0 1) :=
  rank_violation_need_not_be_a_cycle.2

#eval "GRAPH-ALGORITHMS-10000-OK"

-- Same cardinality alone cannot authorize retaining an old component.
example : ([0, 1] : List Nat).length = [0, 2].length ∧
    ¬ (([0, 1] : List Nat) ⊆ [0, 2]) := by decide

-- Enumeration order and representative labels do not define membership.
example : ([0, 1, 2] : List Nat).length = [2, 0, 1].length ∧
    ([0, 1, 2] : List Nat) ⊆ [2, 0, 1] := by decide

-- Equal missing lookups do not create an unchanged component.
example : ¬ LeanPoo.Functional.ComponentWitness.SameComponent
    (fun _ => none) (fun _ => none) 7 :=
  LeanPoo.Functional.ComponentWitness.absent_before_changed rfl

-- Duplicated edges and a cycle preserve the legacy reverse-discovery order.
example : (LeanPoo.Functional.OrderedReachability.indexedRun
    (fun key => if key = 0 then [1, 1] else [0]) 6 [0] [] ∅).2.1 = [1, 0] := by
  let reads : Nat → List Nat := fun key => if key = 0 then [1, 1] else [0]
  have same := congrArg Prod.snd
    (LeanPoo.Functional.OrderedReachability.indexed_prefix_exact reads 6 [0] [] ∅
      LeanPoo.Functional.OrderedReachability.empty_covers).1
  change (LeanPoo.Functional.OrderedReachability.indexedRun reads 6 [0] [] ∅).2.1 =
    (LeanPoo.Functional.OrderedReachability.listRun reads 6 [0] []).2 at same
  rw [same]
  decide
