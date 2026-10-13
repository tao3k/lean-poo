import LeanPoo.Functional.DispatchHandling
import LeanPoo.Object.MultimethodCombination
import LeanPoo.C4.Linearize

namespace LeanPoo.Examples.RecoverableDispatch
open Functional Object MethodCombination

structure Request where
  preferred : Bool
  recover : Bool
  damaged : Bool
  units : Nat
  ceiling : Nat
  label : String

abbrev Args := {request : Request // 0 < request.units}
def input : Codec Args Request String :=
  (Codec.identity Request String).refine (fun request => 0 < request.units) "units"

structure Progress where
  attempts : Nat := 0
  fallback : Nat := 0
  events : List String := []
  deriving BEq
abbrev Action := EStateM String Progress
abbrev Fragment := Contribution Args Action Nat
abbrev Session := DispatchSession Args Fragment Nat Progress String
abbrev Approved := {value : Nat × Nat // 0 < value.1 ∧ value.1 ≤ value.2}
def admit (args : Args) (value : Nat) : Except String Approved :=
  ((Codec.identity (Nat × Nat) String).refine (fun pair => 0 < pair.1 ∧ pair.1 ≤ pair.2) "ceiling").decode
    (value, args.val.ceiling)

def mark (event : String) : Action Unit := modify fun progress => { progress with events := progress.events ++ [event] }

def fallback (args : Args) (_ : String) : Action Nat := do
  mark "fallback"
  modify fun progress => { progress with fallback := progress.fallback+1 }
  return args.val.units + (← get).attempts

def compile : Except String Session := do
  let graph : C4.Graph := { nodes := [{name := "Base"}, {name := "Preferred", parentOrders := [["Base"]]}] }
  let base ← (C4.linearizeVerified graph "Base").mapError (fun _ => "base")
  let preferred ← (C4.linearizeVerified graph "Preferred").mapError (fun _ => "preferred")
  let generic := Multimethod.standard 1
    (fun args : Args => [if args.val.preferred then preferred.output else base.output]) (fun _ => throw "missing")
  let generic ← (generic.contribute [.any] (.around (fun next args => do
    mark s!"enter:{args.val.label}"
    let value ← if args.val.recover then DispatchSession.recoverMethod (next ()) (fallback args) else next ()
    mark s!"exit:{args.val.label}"
    return value))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.any] (.before (fun _ => mark "before"))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Base"] (.primary (fun _ args => do
    mark "base"
    return 2*args.val.units))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Preferred"] (.primary (fun next args => do
    mark "preferred"
    modify fun progress => { progress with attempts := progress.attempts+1 }
    if args.val.damaged then throw "format"
    return (← next ())+1))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.any] (.after (fun _ => mark "after-base"))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Preferred"] (.after (fun _ => mark "after-preferred"))).mapError (fun _ => "registration")
  return ⟨generic, {}⟩

def wire (label : String) (recover damaged : Bool) (ceiling : Nat := 20) : Request :=
  ⟨true,recover,damaged,3,ceiling,label⟩

theorem recovery_uses_failed_progress (action : Action Nat) (args : Args)
    (before retained : Progress) (error : String) (failed : action.run before = .error error retained) :
    (DispatchSession.recoverMethod action (fallback args)).run before = (fallback args error).run retained :=
  DispatchSession.recoverMethod_error _ _ _ _ _ failed

def run : IO Unit := do
  let original ← match compile with | .error error => throw (IO.userError error) | .ok session => pure session
  let recovered := original.call input admit (wire "A" true true)
  unless recovered.outcome.toOption.map (·.val.1) == some 4 && recovered.next.state.attempts == 1 &&
      recovered.next.state.fallback == 1 && recovered.next.state.events ==
        ["enter:A","before","preferred","fallback","exit:A"] do
    throw (IO.userError "fallback restarted old progress or ran after methods after primary failure")
  let valid := recovered.next.call input admit (wire "B" true false)
  unless valid.outcome.toOption.map (·.val.1) == some 7 && valid.reused == some true && valid.next.state.attempts == 2 &&
      (valid.next.state.events.drop recovered.next.state.events.length) ==
        ["enter:B","before","preferred","base","after-base","after-preferred","exit:B"] do
    throw (IO.userError "successful chain changed phase order or cached current arguments")
  let refused := valid.next.call input admit (wire "C" false true)
  unless refused.outcome.toOption.isNone && refused.next.state.attempts == 3 && refused.next.state.fallback == 1 &&
      (refused.next.state.events.drop valid.next.state.events.length) == ["enter:C","before","preferred"] do
    throw (IO.userError "unrecovered method refusal lost progress")
  let rejected := refused.next.call input admit (wire "D" true true 2)
  unless rejected.outcome.toOption.isNone && rejected.next.state.attempts == 4 && rejected.next.state.fallback == 2 &&
      (rejected.next.state.events.drop refused.next.state.events.length) == ["enter:D","before","preferred","fallback","exit:D"] do
    throw (IO.userError "method recovery intercepted output admission or lost its progress")
  let resumed := rejected.next.call input admit (wire "E" true false)
  unless resumed.outcome.toOption.map (·.val.1) == some 7 && resumed.next.state.attempts == 5 do
    throw (IO.userError "resume used old attempt count")
  let batch := original.callBatch input admit [wire "prefix" true true,wire "failure" false true,wire "skipped" true false]
  unless batch.1.toOption.isNone && batch.2.state.attempts == 2 && batch.2.state.fallback == 1 &&
      !(batch.2.state.events.contains "enter:skipped") && original.state.events.isEmpty do
    throw (IO.userError "batch failure lost prefix or applied suffix")
  IO.println "RECOVERABLE-DISPATCH-OK fallback=4 preferred=7 retained-attempts=4 resumed-attempts=5 batch-attempts=2"

#eval run
#print axioms recovery_uses_failed_progress
#print axioms DispatchSession.recoverMethod_handler_error
#print axioms DispatchSession.call_admitted
end LeanPoo.Examples.RecoverableDispatch
