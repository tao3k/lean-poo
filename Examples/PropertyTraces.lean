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

/-- True opens a resource; false requires an existing producer. -/
private def resourceModel : TraceModel Bool Bool Bool :=
  ⟨false, (fun opened command => command || opened),
    (fun opened command => (command || opened, true))⟩

-- Budget zero performs no candidate repair.
example : repairedTracePrefix resourceModel false 0 [[true, false], []] = [] := rfl
-- One full-deletion proposal suffices; an unvisited orphan suffix is irrelevant.
example : repairedTracePrefix resourceModel false 1 [[], [false, false]] = [[]] := rfl
-- Removing the first producer retires its use, retaining later valid dependencies.
example : repairedTracePrefix resourceModel false 2 [[false, true, false], [true, false]] =
    [[true, false], [true, false]] := rfl
-- Restart the next neighborhood from the repaired trace, not the original raw row.
example : repairedTracePrefix resourceModel false 3 [[], [false], [true]] =
    [[], [], [true]] := rfl
-- Structural prefixes preserve exactly the observed finite eager order.
example : repairedTracePrefix resourceModel false 2 [[], [true], [false]] =
    ([[], [true], [false]].map (retire resourceModel false)).take 2 := rfl
-- A nonempty trace strictly decreases even when every parameter has zero cost.
example : traceWeight (fun _ : Bool => 0) [] < traceWeight (fun _ : Bool => 0) [true, false] := by decide

/-- The three-command trace confirms its first smaller failure, then restarts
from that repaired value. A demanded parameter spine refuses after six returned
structural proposals; the refusal is not a seventh proposal. -/
private def resourceRefusalEvents : List (ShrinkEvent (List Bool) String) :=
  ((repairedTracePrefix resourceModel false 3 [[], [false, false], [true, false]] ++
    repairedTracePrefix resourceModel false 3 [[], [false], [true]]).map
      ShrinkEvent.candidate) ++ [.iteratorError "malformed parameter list"]

-- A later iterator error preserves completed work and its exact cause.
example : auditShrinks 64 resourceRefusalEvents =
    ⟨[[], [], [true, false], [], [], [true]], 6, some "malformed parameter list"⟩ := rfl

-- The confirmed producer/use pair survives; error data cannot replace it.
example : shrink (fun commands => traceValid resourceModel false commands)
    (fun commands => commands.contains false) List.length 64 [true, false, false]
    (auditShrinks 64 resourceRefusalEvents).completed = ([true, false], 6) := rfl

-- One original observation and six returned proposals require seven oracle
-- entries. Actual fixture cleanup remains the scoped host caller's obligation.
example : 1 + (auditShrinks 64 resourceRefusalEvents).attempts = 7 := rfl

-- Closed scopes skip a deliberately failing metadata action entirely.
example : admitFixture "scope" (fun _ : Nat => true) false 0
    (fun _ _ => (.error "forbidden metadata" : Except String (Nat × Nat)))
    (fun _ _ => (.error "forbidden run" : Except String (Bool × Nat))) () 0 = .error (some "scope") := rfl

-- An active second use cannot prepare a different raw fixture.
example : admitFixture "scope" (fun _ : Nat => true) true 2
    (fun _ _ => (.error "forbidden metadata" : Except String (Nat × Nat)))
    (fun _ _ => (.error "forbidden run" : Except String (Bool × Nat))) () 0 = .error (some "scope") := rfl

-- Caught duplicate refusal cannot authorize an earlier receipt at final delivery.
example : fixtureReceipt 2 true = false := rfl
example : fixtureReceipt 1 false = false := rfl

-- Type retirement during preparation prevents any actual operation.
example : admitFixture "scope" (fun epoch : Nat => epoch == 0) true 1
    (fun _ _ => (.ok (7, 1) : Except String (Nat × Nat)))
    (fun _ _ => (.error "forbidden run" : Except String (Bool × Nat))) () 0 = .error none := rfl

-- False thrown causes remain distinct from a legitimate false mismatch value.
example : admitFixture true (fun _ : Nat => true) true 1
    (fun _ _ => (.error false : Except Bool (Nat × Nat)))
    (fun _ state => .ok (false, state)) () 0 = .error (some false) := rfl
example : admitFixture "scope" (fun _ : Nat => true) true 1
    (fun raw state => (.ok (raw + 1, state + 1) : Except String (Nat × Nat)))
    (fun value state => .ok (value == 9, state + 1)) 7 0 = .ok (false, 2) := rfl

-- Static bounds reject both sides; the legal empty and maximum requests survive.
example : traceStepLimit (-1) = false := rfl
example : traceStepLimit 65537 = false := rfl
example : traceStepLimit 0 = true := rfl
example : traceStepLimit 65536 = true := rfl

-- No source or fixture preparation occurs after a static request refusal.
example : admitWitness (.ok (traceStepLimit (-1))) "configuration"
    (fun _ => guardedGeneration (fun _ : Nat => true)
      (fun _ => (.error "must not prepare" : Except String (Bool × Nat))) 0) =
        .error (some "configuration") := rfl

-- Valid configuration preserves a legitimate false comparison and resulting state.
example : admitWitness (.ok true) "configuration"
    (fun _ => guardedGeneration (fun _ : Nat => true)
      (fun _ => (.ok (false, 1) : Except String (Bool × Nat))) 0) = .ok (false, 1) := rfl

-- A thrown false cause still differs from the successful false mismatch.
example : admitWitness (.ok true) true
    (fun _ => guardedGeneration (fun _ : Nat => true)
      (fun _ => (.error false : Except Bool (Bool × Nat))) 0) = .error (some false) := rfl

-- Metadata replaces the caller's command row, but execution retains ingress.
example : guardedTraceRequest (fun state : Nat => if state == 0 then [1, 2] else [99])
    (fun _ => true) (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun row _ state => .ok (row, state)) 0 = .ok ([1, 2], 1) := rfl

-- An invalid input is not repaired by metadata into an accepted empty row.
example : guardedTraceRequest
    (fun state : Nat => if state == 0 then none else some ([] : List Nat))
    (fun _ => true) (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun row _ state => match row with
      | none => .error "invalid request"
      | some commands => .ok (commands, state)) 0 = .error (some "invalid request") := rfl

-- A valid empty row and its false payload are retained as ordinary request data.
example : guardedTraceRequest (fun _ : Nat => some ([] : List Bool))
    (fun _ => true) (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun row _ state => .ok (row, state)) 0 = .ok (some [], 1) := rfl
example : guardedTraceRequest (fun _ : Nat => some [false])
    (fun _ => true) (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun row _ state => .ok (row, state)) 0 = .ok (some [false], 1) := rfl

-- Owner substitution cannot retarget the prepared request's identity directory.
example : guardedTraceRequest (fun state : Nat => if state == 0 then [7, 7] else [8])
    (fun _ => true) (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun owners _ state => .ok (owners, state)) 0 = .ok ([7, 7], 1) := rfl

-- Retiring an original owner blocks delivery before execution.
example : guardedTraceRequest (fun _ : Nat => [7]) (fun state => state == 0)
    (fun _ => (.ok ((), 1) : Except String (Unit × Nat)))
    (fun _ _ _ => (.error "must not execute" : Except String (Bool × Nat))) 0 = .error none := rfl

-- A false metadata exception remains an exception even when its owner retires.
example : guardedTraceRequest (fun _ : Nat => [7]) (fun state => state == 0)
    (fun _ => (.error false : Except Bool (Unit × Nat)))
    (fun _ _ state => .ok (false, state)) 0 = .error (some false) := rfl
