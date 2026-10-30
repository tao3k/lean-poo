import LeanPoo.Functional.PropertyReplay

open LeanPoo.Functional.PropertyTesting

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
