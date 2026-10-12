import LeanPoo.Prototype.SharedCellRefinement

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.Recursive.Shared
open LeanPoo.Prototype.SharedCell
open LeanPoo.Prototype.Recursive.Shared.CellRefinement
namespace LeanPoo.Tests.SharedCellRefinement

example (code : Code) (state next : State) (event : Event)
    (transition : step state event = some next) :
    Knot.replay code (project code state) (effect state event) = some (project code next) :=
  step_refines code state next event transition

example (code : Code) (events : List Event) (state : State)
    (transition : replay {} events = some state) (ready : state.stage = .ready) :
    (project code state).code = some code ∧ state.builds = 1 :=
  ready_current code events state transition ready

example (events : List Event) (state : State) (transition : replay {} events = some state) :
    state.cellReads ≤ 1 := at_most_one_cell_read events state transition

example (invocation : Invocation program input events candidate) :
    ∃ depth, solve program depth input = candidate.result := invocation.observed

example : (SharedCell.tie operations).run {} =
    (replay {} SharedCell.construction).map (fun state => (.result, state)) := constructor_is_replay

private def sum : Recursive.Generator Nat Nat
  | 0 => .value 0
  | n + 1 => .call n fun answer => .value (answer + n + 1)

private def repeated : Recursive.Generator Nat Nat
  | 0 => .value 1
  | n + 1 => .call n fun left => .call n fun right => .value (left + right + 1)

private def errorChain : Recursive.Generator Nat Nat
  | 0 => .error "cell-source-error"
  | n + 1 => .call n fun answer => .value (answer + n)

private def changing : Recursive.Generator Nat Nat := fun n => .call (n + 1) .value

private def readyEvents : List Event :=
  SharedCell.construction ++ [.beginResult, .returnResult, .forceResult]

private def firstSelf : List Event :=
  [.beginSelf, .getRef .result, .returnSelf, .forceSelf]

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkedState (events : List Event) : IO State :=
  match check () events with
  | none => throw (IO.userError s!"Refused actual operation log: {repr events}")
  | some receipt => return receipt.state

private unsafe def observedDepth (program : Recursive.Generator Nat Nat)
    (log : IO.Ref (List Event)) : BaseIO (ObservedThunk (FixedFunction (Nat × Nat) (Candidate Nat))) :=
  sharedFixWithObserver (fun self => FixedFunction.ofFun fun (depth, input) =>
    match depth with
    | 0 => ⟨.pending, .cut⟩
    | depth + 1 => record (fun query => (self ()) (depth, query)) (program input))
    (fun event => log.modify (· ++ [event]))

private unsafe def run : IO Unit := do
  expect (Lean.githash == runtimeRevision && Lean.version.major == 4 &&
    Lean.version.minor == 34 && Lean.version.patch == 0)
    "Primitive rules require the reviewed Lean 4.34.0 runtime revision"
  let mut calls := 0
  let mut admitted := 0
  let mut pending := 0
  let mut instances := 0
  let mut hotGets := 0
  let mut pointerChecks := 0
  let mut cellReads := 0
  for program in [sum, repeated, errorChain, changing] do
    for round in List.range 6 do
      let log ← IO.mkRef ([] : List Event)
      let thunk ← observedDepth program log
      let allocated ← checkedState (← log.get)
      expect (allocated.stage == .linked && allocated.builds == 0 && allocated.cellReads == 0)
        s!"Constructor state: {repr allocated}; log={repr (← log.get)}"
      let function ← thunk.get
      instances := instances + 1
      for input in List.range 9 do
        let depth := round * 2
        let candidate := function (depth, input)
        calls := calls + 1
        expect (candidate == recordSolve program depth input) "Native demand/result mismatch"
        let events ← log.get
        let state ← checkedState events
        expect (state.stage == .ready && state.builds == 1 && state.cellReads ≤ 1)
          "Private cell or constructor count changed"
        if candidate.result == .pending then
          expect (admitInvocation program input events candidate |>.isNone)
            "Unfinished candidate admitted"
          pending := pending + 1
        else
          expect (admitInvocation program input events candidate |>.isSome)
            "Completed actual candidate refused"
          admitted := admitted + 1
      for _ in List.range 3 do
        let again ← thunk.get
        expect (ptrEq function again) "Result thunk failed to preserve the cached closure"
        hotGets := hotGets + 1
      let events ← log.get
      let final ← checkedState events
      expect (final.builds == 1 && final.cellReads ≤ 1) "Hot forcing rebuilt/read the cell"
      expect (events.count .beginResult == 1 && events.count .returnResult == 1)
        "Native result closure executed more than once"
      expect (events.count .beginSelf == final.cellReads && events.count .returnSelf == final.cellReads)
        "Forwarding thunk did not cache its cell read"
      expect (events.count (.verify true) == 2 && events.count (.verify false) == 0)
        "Native pointer readback failed"
      pointerChecks := pointerChecks + 2
      cellReads := cellReads + final.cellReads

  -- Independent arithmetic, with recursive calls through the actual self.
  let sumLog ← IO.mkRef ([] : List Event)
  let actual ← observedDepth sum sumLog
  let function ← actual.get
  for input in List.range 20 do
    expect ((function (25, input)).result == .value (input * (input + 1) / 2))
      "Independent triangular-number control failed"

  -- Each delayed value stays cold until forced, then runs its body once.
  let mut delayedGets := 0
  for seed in List.range 32 do
    let log ← IO.mkRef ([] : List Event)
    let counter ← IO.mkRef 0
    let thunk ← sharedFixWithObserver (fun (_ : Unit → Nat) => unsafeBaseIO do
      counter.modify (· + 1)
      return seed * 7 + 3) (fun event => log.modify (· ++ [event]))
    expect ((← counter.get) == 0) "Delayed body ran during construction"
    for _ in List.range 4 do
      expect ((← thunk.get) == seed * 7 + 3) "Delayed value changed"
      delayedGets := delayedGets + 1
    let state ← checkedState (← log.get)
    expect ((← counter.get) == 1 && state.builds == 1 && state.cellReads == 0)
      "Delayed value rebuilt or read self"

  -- Two simultaneously retained cells remain distinct under interleaved calls.
  let firstLog ← IO.mkRef ([] : List Event)
  let secondLog ← IO.mkRef ([] : List Event)
  let first ← observedDepth sum firstLog
  let second ← observedDepth repeated secondLog
  let firstFunction ← first.get
  let secondFunction ← second.get
  for input in List.range 9 do
    expect ((firstFunction (20, input)).result == .value (input * (input + 1) / 2)) "First cell changed"
    expect ((secondFunction (20, input)).result == .value (2 ^ (input + 1) - 1)) "Second cell changed"
  for log in [firstLog, secondLog] do
    let state ← checkedState (← log.get)
    expect (state.builds == 1 && state.cellReads == 1) "Interleaved cells lost sharing"

  -- These controls distinguish return from publication and busy self from a
  -- completed self get. Early native forcing would wait; we check that branch
  -- in the terminating model, without inventing a native exception.
  let bad := [
    [.mkRef],
    SharedCell.construction ++ [.beginResult, .beginResult],
    SharedCell.construction ++ [.beginResult, .forceResult],
    SharedCell.construction ++ [.beginResult, .beginSelf, .getRef .result, .forceResult],
    readyEvents ++ [.setRef .result],
    readyEvents ++ [.beginSelf, .getRef .unavailable],
    readyEvents ++ [.beginSelf, .getRef .result, .getRef .result],
    readyEvents ++ [.forceSelf],
    readyEvents ++ [.beginSelf, .getRef .result, .forceSelf],
    readyEvents ++ firstSelf ++ [.beginSelf],
    readyEvents ++ firstSelf ++ [.getRef .result],
    readyEvents ++ [.verify false]]
  for events in bad do expect (check () events |>.isNone) "Malformed primitive trace admitted"
  let returnedOnly := SharedCell.construction ++ [.beginResult, .returnResult]
  expect (check () returnedOnly |>.isSome) "Closure-return prefix should be valid"
  expect (admitInvocation sum 0 returnedOnly ⟨.value 0, .value⟩ |>.isNone)
    "Body return was treated as published cache"
  expect (admitInvocation sum 0 readyEvents ⟨.value 99, .value⟩ |>.isNone)
    "Wrong native result admitted"
  expect (admitInvocation errorChain 0 readyEvents ⟨.error "changed-error", .error⟩ |>.isNone)
    "Wrong native error admitted"
  expect (admitInvocation errorChain 0 readyEvents (recordSolve sum 1 0) |>.isNone)
    "Retained candidate accepted against changed program"
  IO.println s!"SHARED-CELL-REFINEMENT-OK instances={instances} calls={calls} admitted={admitted} pending={pending} hotGets={hotGets} pointerChecks={pointerChecks} firstCellReads={cellReads} delayedGets={delayedGets} malformed={bad.length} admissionRefusals=4 independent=38"

#eval run
#print axioms step_refines
#print axioms replay_refines
#print axioms constructor_is_replay
#print axioms at_most_one_cell_read
#print axioms Invocation.observed
end LeanPoo.Tests.SharedCellRefinement
