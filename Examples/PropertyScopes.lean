import LeanPoo.Functional.PropertyScopes

/-! Transient replay owners and new-run publication are distinct directories. -/
open LeanPoo.Functional.PropertyTesting

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
