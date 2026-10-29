import LeanPoo.Functional.PropertyTraces

/-! Scoped revision and first-difference controls for the finite trace protocol. -/
open LeanPoo.Functional.PropertyTesting

example : guardedTraceStep (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (1, 0) : Except String (Nat × Nat)))
    (fun _ => (.ok (1, 1) : Except String (Nat × Nat)))
    (fun _ _ _ => .error "comparison must not run") 0 = .error none := rfl

example : guardedTraceStep (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (1, 0) : Except String (Nat × Nat)))
    (fun _ => (.ok (1, 0) : Except String (Nat × Nat)))
    (fun _ _ _ => .ok (true, 1)) 0 = .error none := rfl

example : guardedTraceStep (fun _ : Nat => true)
    (fun _ => (.ok (1, 0) : Except String (Nat × Nat)))
    (fun _ => (.error "fixture failure" : Except String (Nat × Nat)))
    (fun _ _ _ => .ok (true, 0)) 0 = .error (some "fixture failure") := rfl

example : guardedTraceStep (fun _ : Nat => true)
    (fun _ => (.ok (1, 0) : Except String (Nat × Nat)))
    (fun _ => (.ok (99, 0) : Except String (Nat × Nat)))
    (fun expected actual state => .ok (expected == actual, state)) 0 = .ok (false, 0) := rfl
