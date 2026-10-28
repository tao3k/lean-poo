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

-- Sibling draws start from the same checkpoint despite consuming different states.
example : regenerateCheckpoint id (fun (n state : Nat) =>
    (Except.ok (n + state, state + n) : Except String (Nat × Nat))) 5 [3, 2, 1] =
    .ok [(8, 8), (7, 7), (6, 6)] := by rfl
example : regenerateCheckpoint id (fun (n state : Nat) =>
    if n = 2 then (Except.error "refused" : Except String (Nat × Nat))
    else .ok (n, state + n)) 5 [3, 2, 1] = .error "refused" := by rfl
example : checkpointExpansions 0 = 0 := by decide
example : checkpointExpansions 20 = 1 := by decide

-- Discards do not fabricate coverage; a later effective trial contributes once.
example : (recordTrial (recordTrial ({} : TrialLedger String) false ["retry"]) true ["retry"]).labels =
    ["retry"] := by decide
example : (recordTrial (recordTrial ({} : TrialLedger String) false []) true ["retry"]).accepted = 1 := by decide

-- A changed application identity refuses before decoding a stored witness.
example : decodeReplay "v2" (fun (n : Nat) => some n)
    ({ identity := "v1", payload := 4 } : ReplayEnvelope String Nat) = none := by decide
example : decodeReplay "v1" (fun (n : Nat) => some n)
    ({ identity := "v1", payload := 4 } : ReplayEnvelope String Nat) = some 4 := by decide

-- Argument rows can include keyword interpretation codes; tuples retain multiple results.
example : lookupFunction [([1, 7, 2], [4, 5]), ([2], [9, 10])] [1, 7, 2] = some [4, 5] := by decide
example : lookupFunction [([1, 7, 2], [4, 5]), ([2], [9, 10])] [99] = none := by decide
example : lookupFunction ([([1], [8, 8])].map
    (fun entry => (entry.1, entry.2.map (fun n => n / 2)))) [1] = some [4, 4] := by decide
