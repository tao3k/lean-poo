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
