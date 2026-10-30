import LeanPoo.Functional.PropertyScopes

/-! Transient replay owners and new-run publication are distinct directories. -/
open LeanPoo.Functional.PropertyTesting

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
