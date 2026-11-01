import LeanPoo.Functional.PropertyReplay

open LeanPoo.Functional.PropertyTesting

-- A fresh symbol in a nested directory skips every writer/decoder continuation.
example : admitReplayTokens id [true, false] "nonportable"
    (fun _ : Nat => (.error (some "must not decode") : Except (Option String) Bool)) 0 =
      .error (some "nonportable") := rfl
-- A fresh keyword is refused by the same rule, without silently interning it.
example : admitReplayTokens (fun token : Nat => token < 2) [0, 2] false
    (fun _ : Nat => (.ok true : Except (Option Bool) Bool)) 0 = .error (some false) := rfl
-- Empty token directories preserve false data and the existing action state.
example : admitReplayTokens id [] "nonportable"
    (fun state : Nat => (.ok (false, state + 1) : Except (Option String) (Bool × Nat))) 0 =
      .ok (false, 1) := rfl
-- Admitted interned tokens retain the original callback's false cause.
example : admitReplayTokens id [true, true] true
    (fun _ : Nat => (.error (some false) : Except (Option Bool) Bool)) 0 = .error (some false) := rfl
-- Old epoch refusal is still distinct from a nonportable-token error.
example : admitReplayTokens id [true] "nonportable"
    (fun _ : Nat => (.error none : Except (Option String) Bool)) 0 = .error none := rfl

-- An impossible width cannot reach destination allocation or child admission.
example : admitReplayVector 7 4 64
    (fun _ => (.error "nonportable first child" : Except String Nat)) = .error none := rfl

-- Exact positive child credits fit; one fewer credit refuses the same profile.
example : replayCopyCosts [3, 3, 1] 7 = some 0 := rfl
example : replayCopyCosts [3, 3, 1] 6 = none := rfl

-- Empty vectors are valid at depth zero, including after an enclosing root.
example : admitReplayVector 0 0 0 (fun width => (.ok width : Except String Nat)) = .ok 0 := rfl

-- Child inspection preserves its cause once width/depth admission succeeds.
example : admitReplayVector 7 1 2
    (fun _ => (.error "first invalid child" : Except String Nat)) =
      .error (some "first invalid child") := rfl

-- A reader EOF marker with pending physical input refuses, without a decoder.
example : replayInputEnd (fun _ : Nat => true) "trailing"
    (fun _ => .ok (true, 1)) (fun _ => .ok (false, 2)) 0 = .error (some "trailing") := rfl

-- Complete physical EOF preserves the port-observation state.
example : replayInputEnd (fun _ : Nat => true) "trailing"
    (fun _ => .ok (true, 1)) (fun _ => .ok (true, 2)) 0 = .ok ((), 2) := rfl

-- Static request failure wins before a stale or effectful action is entered.
example : admitReplayRequest false "configuration"
    (fun _ : Nat => (.error none : Except (Option String) Bool)) 0 =
      .error (some "configuration") := rfl

-- Source retirement after reader return skips the physical action entirely.
example : replayInputEnd (fun state : Nat => state == 0) "trailing"
    (fun _ => .ok (true, 1)) (fun _ => .error "must not run") 0 = .error none := rfl

-- False callback causes are tagged exceptions, never successful false witnesses.
example : replayInputEnd (fun _ : Nat => true) true
    (fun _ => .error false) (fun _ => .ok (true, 0)) 0 = .error (some false) := rfl
