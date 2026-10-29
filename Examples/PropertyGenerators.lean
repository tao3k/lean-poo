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


-- A delayed standard check cannot admit a stale former pass.
example : checkedStatus .passed false = .stale := by decide
example : checkedStatus .coverage true = .coverage := by decide
example : checkedStatus .exhausted true = .exhausted := by decide
example : checkedStatus .error true = .error := by decide
example : productDomain [(fun n : Nat => n < 3), (fun n => n = 5)] [2, 5] = true := by decide
example : productDomain [(fun n : Nat => n < 3), (fun n => n = 5)] [2, 4] = false := by decide
example : productDomain [(fun n : Nat => n < 3)] [2, 4] = false := by decide

-- Unicode boundary controls and fixed byte widths match the generic data families.
example : scalarCode 0xd7ff = 0xd7ff := by decide
example : scalarCode 0xd800 = 0xe000 := by decide
example : scalarCode 0x10f7ff = 0x10ffff := by decide
example : intervalValue 0 255 = 255 := by decide
example : dataLength 4 0 0 0 = 4 := by decide
example : intervalValue 97 0 = 97 := by decide

-- Inspection refuses nondecreasing/out-of-domain proposals and bounds cyclic neighborhoods.
example : inspectionAdmission (fun n : Nat => n < 10) id 8 4 = true := by decide
example : inspectionAdmission (fun n : Nat => n < 10) id 8 8 = false := by decide
example : inspectionAdmission (fun n : Nat => n < 3) id 8 4 = false := by decide
example : inspectionWalk 2 3 [(0, 4)] (fun n : Nat => [n]) = [(0, 4), (1, 4), (2, 4)] := by decide
example : inspectionWalk 0 3 [(0, 4)] (fun n : Nat => [n]) = [(0, 4)] := by decide
example : inspectionWalk 99 0 [(0, 4)] (fun n : Nat => [n]) = [] := by decide

-- Default test/debug integration keeps configuration revisions and refusal evidence.
example : configuredCheck (⟨.passed, true, [("input", 4)], none⟩ : CheckDiagnostics Nat String) 1 2 ≠ .ok () := by simp [configuredCheck_ok]
example : configuredCheck (⟨.passed, true, [("input", 4)], none⟩ : CheckDiagnostics Nat String) 2 2 = .ok () := by simp [configuredCheck_ok]
example : debugDelivery false (fun n : Nat => n + 1) 4 = (4, none) := by decide
example : configurationLimit (some 20) none = some 20 := by decide
example : configurationLimit none none = none := by decide

-- Middle/tail deletions preserve endpoints and map the retained objects only.
example : deleteBlock [11, 99, 22] 1 1 = [11, 22] := by decide
example : deleteBlock [11, 99, 22] 2 1 = [11, 99] := by decide
example : deleteBlock [11, 99, 22] 0 3 = ([] : List Nat) := by decide

-- Codec/domain revisions refuse before delivery; callback causes remain exact.
example : replayStage false true (fun _ => (.ok 4 : Except String Nat)) = .error none := rfl
example : replayStage true false (fun _ => (.ok 4 : Except String Nat)) = .error none := rfl
example : replayStage true false (fun _ => (.error "decode" : Except String Nat)) =
    .error (some "decode") := rfl
example : (replayStage true false (fun _ => (.ok 4 : Except String Nat)) >>=
    fun n => (.ok (n + 1) : Except (Option String) Nat)) = .error none := rfl
example : (replayStage true true (fun _ => (.ok 4 : Except String Nat)) >>=
    fun n => (.ok (n + 1) : Except (Option String) Nat)) = .ok 5 := rfl

-- Concrete witnesses retain preconditions and do not re-run coverage admission.
example : checkWitness (fun _ => .ok false) (fun _ => .ok true)
    (fun _ => .ok false) "excluded" = .error (some "excluded") := rfl
example : checkWitness (fun _ => replayStage true false (fun _ => (.ok true : Except String Bool)))
    (fun _ => .ok true) (fun _ => .ok false) "excluded" = .error none := rfl
example : checkWitness (fun _ => .ok true) (fun _ => .ok true)
    (fun _ => .ok false) "excluded" = .ok false := rfl
example : checkWitness (fun _ => .ok true) (fun _ => .error (some "recognizer"))
    (fun _ => .ok false) "excluded" = .error (some "recognizer") := rfl

-- A revision is an intermediate state change, not a later property failure.
example : guardedGeneration (fun n : Nat => n == 0)
    (fun _ => (.ok (7, 1) : Except String (Nat × Nat))) 0 = .error none := rfl
example : (guardedGeneration (fun n : Nat => n == 0)
    (fun _ => (.ok (7, 1) : Except String (Nat × Nat))) 0 >>=
      fun pair => (.ok pair.1 : Except (Option String) Nat)) = .error none := rfl
example : guardedGeneration (fun n : Nat => n < 2)
    (fun _ => (.ok (7, 1) : Except String (Nat × Nat))) 0 = .ok (7, 1) := rfl
example : guardedGeneration (fun n : Nat => n == 0)
    (fun _ => (.error "draw" : Except String (Nat × Nat))) 0 = .error (some "draw") := rfl

-- Fixed finite keys distinguish absence from a stored false value.
example : selectedHashKeys [0, 1, 2] (fun n => n != 1) 1 = [0] := by decide
example : selectedHashKeys [0, 1, 2] (fun _ => true) 0 = [] := by decide
example : lookupFunction (hashEntries [1, 3] (fun _ => false)) 1 = some false := by decide
example : lookupFunction (hashEntries [1, 3] (fun _ => false)) 2 = none := by decide
example : deleteBlock (hashEntries [1, 2, 3] (fun n => n * 2)) 1 1 = [(1, 2), (3, 6)] := by decide

-- Declared enum order is a simplification policy; equal duplicates use their first rank.
example : enumChoice [false, true, false] 0 = some false := rfl
example : enumChoice [false, true, false] 3 = none := rfl
example : enumRank [false, true, false] false = 0 := rfl
example : enumRank ["read", "write", "admin"] "write" <
    enumRank ["read", "write", "admin"] "admin" := by decide

/-- A finite producer/consumer model with parity-sensitive independent noise. -/
private def traceBlocks : TraceModel (Bool × Nat) Nat Unit where
  initial := (false, 0)
  enabled := fun state command => if command == 1 then !state.1 else if command == 2 then state.1 else true
  advance := fun state command =>
    ((if command == 1 then (true, state.2) else if command == 0 then (state.1, state.2 + 1) else state), ())

/-- A consumer fault survives zero or two noise commands, but not one. -/
private def parityFault (commands : List Nat) : Bool :=
  commands.contains 2 && ((commands.filter (· == 0)).length % 2 == 0)

example : repairedBlock traceBlocks traceBlocks.initial [0, 0, 1, 2] 0 2 = [1, 2] := by decide
example : parityFault [0, 0, 1, 2] = true ∧ parityFault [0, 1, 2] = false ∧
    parityFault [1, 2] = true := by decide
example : repairedBlock traceBlocks traceBlocks.initial [0, 0, 1, 2] 2 1 = [0, 0] := by decide
example : traceValid traceBlocks traceBlocks.initial
    (repairedBlock traceBlocks traceBlocks.initial [0, 0, 1, 2] 0 2) = true := by decide
example : traceWeight (fun _ => 0) (repairedBlock traceBlocks traceBlocks.initial [0, 0, 1, 2] 0 2) <
    traceWeight (fun _ => 0) [0, 0, 1, 2] := by decide

-- Source revisions at a product boundary prevent every later field effect.
example : guardedStages (fun epoch : Nat => epoch == 0)
    [(fun _ => (.ok (true, 1) : Except String (Bool × Nat))),
     (fun _ => .error "later field ran")] 0 = .error none := rfl
example : guardedStages (fun epoch : Nat => epoch == 0)
    [(fun _ => (.ok (true, 0) : Except String (Bool × Nat))),
     (fun _ => .ok (false, 1)), (fun _ => .error "third field ran")] 0 = .error none := rfl
example : guardedStages (fun _ : Nat => true)
    [(fun _ => (.error "field cause" : Except String (Bool × Nat))),
     (fun _ => .error "later field ran")] 0 = .error (some "field cause") := rfl

-- Stale policy results refuse regardless of the Boolean; stable exclusions skip evaluation.
example : guardedShrinkPolicy (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (true, 1) : Except String (Bool × Nat)))
    (fun _ => .error (some "property ran")) 0 = .error none := rfl
example : guardedShrinkPolicy (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ => .error (some "property ran")) 0 = .error none := rfl
example : guardedShrinkPolicy (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 0) : Except String (Bool × Nat)))
    (fun _ => .error (some "property ran")) 0 = .ok (true, 0) := rfl
example : guardedShrinkPolicy (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (true, 0) : Except String (Bool × Nat)))
    (fun _ => .error (some "property cause")) 0 = .error (some "property cause") := rfl
