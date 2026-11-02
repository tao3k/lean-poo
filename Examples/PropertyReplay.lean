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

-- Malformed codec authority wins before a throwing context or decoder runs.
example : checkedReplayAction "malformed" "codec stale" "context stale"
    (fun _ : Nat => .ok none) (fun _ => .error "must not observe")
    (fun _ => (.error "must not decode" : Except String (Bool × Nat))) 0 = .error "malformed" := rfl
-- False is retirement; throwing false remains a separate exact cause.
example : replayAuthority true true true (fun _ : Nat => .error false)
    (fun _ => .ok (some true)) 0 = .error false := rfl
-- Normal decoding can change the codec reply; that value is never published.
example : checkedReplayAction "malformed" "codec stale" "context stale"
    (fun state : Nat => .ok (if state = 0 then some true else none))
    (fun _ => .ok (some true)) (fun _ => .ok (false, 1)) 0 = .error "malformed" := rfl
-- Failed delivery preserves its own false cause rather than consulting a trailer.
example : checkedReplayAction true true true
    (fun _ : Nat => .ok (some true)) (fun _ => .ok (some true))
    (fun _ => (.error false : Except Bool (Bool × Nat))) 0 = .error false := rfl
-- A fresh lawful attempt preserves false data and its exact state.
example : checkedReplayAction "malformed" "codec stale" "context stale"
    (fun _ : Nat => .ok (some true)) (fun _ => .ok (some true))
    (fun _ => .ok (false, 1)) 0 = .ok (false, 1) := rfl


-- A computed execution getter retires an explicit extra owner before handoff.
example : replayHandoff (fun _ : Nat => true) (fun _ => true) (fun epoch _ : Nat => epoch)
    [(7, 0)] (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ _ _ => (.error (some "must not replay") : Except (Option String) Bool)) 0 = .error none := rfl
-- Thrown false remains an exact getter cause, not the absent stale sentinel.
example : replayHandoff (fun _ : Nat => true) (fun _ => true) (fun _ _ : Nat => 0)
    [(7, 0)] (fun _ => (.error false : Except Bool (Bool × Nat)))
    (fun _ _ _ => (.ok true : Except (Option Bool) Bool)) 0 = .error (some false) := rfl
-- Publication retains the old captured row even if later host metadata differs.
example : replayHandoff (fun _ : Nat => true) (fun _ => true) (fun _ _ : Nat => 0)
    [(7, 0)] (fun state => (.ok (false, state) : Except String (Bool × Nat)))
    (fun _ _ _ => (.ok false : Except (Option String) Bool)) 0 = .ok (false, [(7, 0)]) := rfl
-- A classified error receipt is data; no added post-check masks its original cause.
example : replayHandoff (fun epoch : Nat => epoch == 0) (fun _ => true) (fun _ _ : Nat => 0)
    [(7, 0)] (fun state => (.ok (false, state) : Except Bool (Bool × Nat)))
    (fun _ _ _ => (.ok (Except.error false) : Except (Option Bool) (Except Bool Bool))) 0 =
      .ok (Except.error false, [(7, 0)]) := rfl
-- A new clock cannot turn an old declared epoch into a fresh source snapshot.
example : replayHandoff (fun _ : Nat => true) (fun _ => true) (fun epoch _ : Nat => epoch)
    [(7, 0)] (fun state => (.ok (false, state) : Except String (Bool × Nat)))
    (fun _ _ _ => (.ok false : Except (Option String) Bool)) 1 = .error none := rfl
