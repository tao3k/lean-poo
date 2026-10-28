import LeanPoo.Functional.PropertyGenerators

/-! Concrete negative/positive controls for weighted choices and charged pruning. -/
open LeanPoo.Functional.PropertyTesting

example : weightedChoice [(0, 99), (3, 7), (1, 8)] 0 = some 7 := by decide
example : weightedChoice [(0, 99), (3, 7), (1, 8)] 3 = some 8 := by decide
example : weightedChoice [(0, 99)] 0 = none := by decide
example : weightedChoice [(2, 7)] 2 = none := by decide

example : scheduledSamples (fun seed size => (size + seed, seed + 1))
    (fun trial => trial * 2) 3 1 0 = [(2, 2), (4, 5), (6, 8)] := by decide

example : shrinkProposals (fun (_ : Nat) => true) (fun _ => true) id 1 9
    [.pruned, .value 0] = (9, 1) := by decide
example : shrinkProposals (fun (_ : Nat) => true) (fun _ => true) id 2 9
    [.pruned, .value 0] = (0, 2) := by decide
example : shrinkProposals (fun (_ : Nat) => true) (fun _ => true) id 0 9
    [.value 0] = (9, 0) := by decide
