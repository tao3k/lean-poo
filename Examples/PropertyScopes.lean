import LeanPoo.Functional.PropertyScopes

/-! Transient replay owners and new-run publication are distinct directories. -/
open LeanPoo.Functional.PropertyTesting

-- An inherited integer grammar cannot become a distinct exact-value declaration.
example : prepareSampler (0 : Nat) 1 2 [] = .error () := rfl

-- Explicit construction binds the new declaration and retains its actual Type.
example : prepareSampler (0 : Nat) 2 2 [] = .ok [0, 2] := rfl

-- Replacing optional dependencies with an empty list cannot hide a retired Type.
example : (samplerOwners (0 : Nat) 1 []).all (fun source => source != 1) = false := by decide

-- A known sibling retains epoch zero even if a factory tries to capture epoch one.
example : captureRevision [(0, 0), (1, 0)] 1 1 = [(0, 0), (1, 0)] := by decide

-- Discovering another owner cannot make a previously changed source current.
example : revisionsCurrent (fun _ : Nat => 1) (captureRevision [(0, 0)] 1 1) = false := by decide

-- An early factory revises the already discovered sibling; its later factory is skipped.
example : guardedStages
    (fun state : Nat × List (Nat × Nat) => revisionsCurrent (fun _ => state.1) state.2)
    [(fun _ => (.ok (9, (1, [(0, 0), (1, 0)])) : Except String (Nat × (Nat × List (Nat × Nat))))),
     (fun _ => .error "later factory must not run")]
    (0, [(0, 0), (1, 0)]) = .error none := rfl

-- A decoder's own node has no sources, but inherited codec authority stops its mapper.
example : scopedStages (fun epoch source : Nat => source != 0 || epoch == 0) [0]
    [(fun _ => (.ok (9, (1, [])) : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .error "nested packing must not run")] (0, []) = .error none := rfl

-- Codec and application ownership both participate throughout nested decoding.
example : scopedStages (Cause := String) (fun _ _ : Nat => true)
    (mergeSources [0] [1]) [fun state => .ok (9, state)] (0, []) = .ok ([9], (0, [])) := rfl

-- An original decoder exception bypasses delivery and retains its identity.
example : scopedStages (fun epoch source : Nat => source != 0 || epoch == 0) [0]
    [(fun _ => (.error "original decoder cause" : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .error "delivery must not run")] (0, []) = .error (some "original decoder cause") := rfl

-- Recipe replacement during error interpretation retires the normal status.
example : classifyFailure (Secondary := String) (fun epoch : Nat => epoch == 0)
    (fun _ => .ok (.unsupported, 1)) "service unavailable" 0 =
      (.stale, "service unavailable") := rfl

-- A secondary classification exception never overwrites the service failure.
example : classifyFailure (fun _ : Nat => true)
    (fun _ => (.error "classifier failed" : Except String (CheckStatus × Nat)))
    "service unavailable" 0 = (.error, "service unavailable") := rfl

-- Explicit fresh preparation may classify again under the new recipe epoch.
example : classifyFailure (Secondary := String) (fun epoch : Nat => epoch == 1)
    (fun epoch => .ok (.unsupported, epoch)) "service unavailable" 1 =
      (.unsupported, "service unavailable") := rfl

-- Source 0 belongs only to the prior run. Its revision still suppresses mapping,
-- although the newly observed source 1 remains live.
example : scopedStages (fun epoch source : Nat => source != 0 || epoch == 0) [0]
    [(fun _ => (.ok (9, (1, [1])) : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .error "later construction must not run")] (0, []) = .error none := rfl

-- Successful observation publishes the actual new ledger [1], not replay owner [0].
example : scopedStages (Cause := String) (fun _ _ : Nat => true) [0]
    [fun _ => .ok (9, (0, [1]))] (0, []) = .ok ([9], (0, [1])) := rfl

-- An empty observation is also refused when its transient authority is obsolete.
example : scopedStages (Cause := String) (Value := Nat) (fun _ _ : Nat => false) [0]
    [] (0, []) = .error none := rfl

-- An original callback exception is not replaced with a fabricated stale result.
example : scopedStages (fun _ _ : Nat => true) [0]
    [(fun _ => (.error "exact callback" : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .error "later callback")] (0, []) = .error (some "exact callback") := rfl

-- Initialization changes the source epoch: no dependent draw/actual effect runs.
example : guardedThen (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ _ => (.error "draw must not run" : Except String (Bool × Nat))) 0 = .error none := rfl

-- A model's two-value transition can feed the actual comparison without loss.
example : guardedThen (fun _ : Nat => true)
    (fun _ => (.ok ((1, false), 0) : Except String ((Nat × Bool) × Nat)))
    (fun result epoch => .ok (result.2, epoch)) 0 = .ok (false, 0) := rfl

-- A later observer revision suppresses publication even after a fresh first stage.
example : guardedThen (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 0) : Except String (Bool × Nat)))
    (fun _ _ => .ok (true, 1)) 0 = .error none := rfl

-- A child domain remains locally fresh; ancestor revision still blocks packing.
example : nestedActions (fun epoch : Nat => epoch == 0) (fun _ => true)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ _ => (.error "packing must not run" : Except String (Nat × Nat))) 0 = .error none := rfl

-- A diagnostic is allowed under a live parent without re-running its local guard.
example : guardedGeneration (fun _ : Nat => true)
    (fun _ => (.ok ("child-stale", 1) : Except String (String × Nat))) 0 =
      .ok ("child-stale", 1) := rfl
