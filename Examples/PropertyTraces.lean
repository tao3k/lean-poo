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


-- Unrepresentable/non-natural configurations refuse before initialization.
example : configuredDraw (State := Nat) (Command := Bool) (Reply := Unit)
    ⟨0, (fun _ _ => true), (fun state _ => (state + 1, ()))⟩
    (fun _ _ _ => some false) (fun _ => .error "initializer must not run")
    "disabled" none = .error none := rfl

-- False is a command payload; the stop marker remains Option.none.
example : configuredDraw (State := Nat) (Command := Bool) (Reply := Unit)
    ⟨0, (fun _ _ => true), (fun state _ => (state + 1, ()))⟩
    (fun _ _ _ => some false) (fun _ => (.ok 0 : Except String Nat))
    "disabled" (some (3, 2)) = .ok [false, false] := rfl

-- A valid zero cap preserves an initializer exception instead of hiding it.
example : configuredDraw (State := Nat) (Command := Bool) (Reply := Unit)
    ⟨0, (fun _ _ => true), (fun state _ => (state + 1, ()))⟩
    (fun _ _ _ => none) (fun _ => .error "initial cause") "disabled" (some (0, 2)) =
      .error (some "initial cause") := rfl


-- An unchanged state can still make different observed choices as fuel decreases.
example : configuredDraw (State := Unit) (Command := Bool) (Reply := Unit)
    ⟨(), (fun _ _ => true), (fun _ _ => ((), ()))⟩
    (fun _ _ remaining => some (remaining == 1))
    (fun _ => (.ok () : Except String Unit)) "disabled" (some (2, 2)) =
      .ok [true, false] := rfl
