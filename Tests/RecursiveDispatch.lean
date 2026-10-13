import LeanPoo.Functional.RecursiveDispatch
import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Tests.RecursiveDispatch
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object Object.MethodCombination
open Functional.RecursiveDispatch
variable {program : Self Dynamic.Value}
def schema (rate : Int) : Object.Callable.Schema Dynamic.Value :=
  ⟨[("Service", ["Fee", "Tariff"]), ("Fee", ["Base"]), ("Tariff", ["Base"]), ("Base", [])],
    fun name =>
      if name == "Tariff" then method "rate" (constant (.integer rate))
      else if name == "Fee" then method "quote" (modify fun _ value => match value with
        | .integer price => .integer (price + 2) | _ => .unit)
      else if name == "Base" then Prototype.composeAll [
        method "rate" (constant (.integer 1)),
        method "quote" (compute fun self argument => match argument with
          | .integer units => (self ⟨"rate", .unit⟩).map fun value => match value with
            | .integer rate => .integer (units * rate) | _ => .unit
          | _ => .error "integer units required"),
        method "series" (compute fun self argument => match argument with
          | .integer units => if units ≤ 0 then .value (.integer 0) else
            (self ⟨"series", .integer (units - 1)⟩).bind fun previous =>
            (self ⟨"quote", .integer units⟩).bind fun current =>
            match previous, current with
            | .integer previous, .integer current => .value (.integer (previous + current))
            | _, _ => .error "integer prices required"
          | _ => .error "integer units required"),
        method "unavailable" (fun _ _ _ => .error "supplier unavailable"),
        method "cycle" (compute fun self argument => self ⟨"cycle", argument⟩)]
      else Prototype.identity, {}⟩

def registry (ceiling : Int) : Except Dynamic.SchemaError Dynamic.Registry := do
  let registry : Dynamic.Registry := { descriptors := [
    ("Units", ⟨"Units", .integerRange 0 6, []⟩),
    ("Limit", ⟨"Limit", .integerRange 0 ceiling, []⟩),
    ("Input", ⟨"Input", .named "Units", []⟩),
    ("Output", ⟨"Output", .named "Limit", []⟩),
    ("Unit", ⟨"Unit", .unit, []⟩), ("Any", ⟨"Any", .top, []⟩)] }
  let (registry, _) ← Dynamic.DescriptorFactory.functionOf.call registry "Price"
    [.descriptor "Input", .descriptor "Output"]
  let (registry, _) ← Dynamic.DescriptorFactory.functionOf.call registry "Status"
    [.descriptor "Unit", .descriptor "Any"]
  return registry



structure Args where
  series : Bool
  units : Int
  registry : Dynamic.Registry
  publicLimit : Int
abbrev Action (program : Self Dynamic.Value) := EStateM (RecursiveDispatch.Error program) (RecursiveDispatch.State program (List String))
abbrev Fragment (program : Self Dynamic.Value) := Contribution Args (Action program) (Answer program)
abbrev Session (program : Self Dynamic.Value) := DispatchSession Args (Fragment program) (Answer program)
  (RecursiveDispatch.State program (List String)) (RecursiveDispatch.Error program)
def mark (event : String) : Action program Unit := modify fun state => { state with ledger := state.ledger ++ [event] }
def generic (program : Self Dynamic.Value) := do
  let initial : Multimethod Args (Fragment program) (Action program (Answer program)) := Multimethod.standard 2
    (fun args => [[if args.series then "Bulk" else "Single","Base"],["Card","Channel"]])
    (fun _ => throw (RecursiveDispatch.Error.application (program := program) "missing"))
  let primary ← initial.contribute [.prototype "Base",.prototype "Channel"] (.primary (fun _ args => do
    mark "call"
    callPacked args.registry ⟨⟨if args.series then "series" else "quote","Price",none,false⟩,.integer args.units⟩ 200 60))
  let around ← primary.contribute [.any,.any] (.around (fun next _ => do
    mark "enter"; let answer ← next (); mark "exit"; return answer))
  around.contribute [.any,.any] (.after (fun _ => mark "after"))
def admit (args : Args) (answer : Answer program) : Except (RecursiveDispatch.Error program) (Answer program) :=
  match answer.receipt.invocation.checked.value with
  | .integer price => if price ≤ args.publicLimit then .ok answer else .error (.application "ceiling")
  | _ => .error (.application "integer")
def call (session : Session program) (args : Args) := session.call (Codec.identity Args (RecursiveDispatch.Error program)) admit args

def phase (outcome : Except (DispatchFailure (RecursiveDispatch.Error program)) (Answer program)) : String × Option Dynamic.Value :=
  match outcome with
  | .ok answer => ("ok",some answer.receipt.invocation.checked.value)
  | .error (.method (.recursive (.boundary (.argument _)))) => ("input",none)
  | .error (.method (.recursive (.boundary (.result _)))) => ("recursive-output",none)
  | .error (.output _) => ("public-output",none)
  | _ => ("unexpected",none)

def control (rate : Int) (series : Bool) (units ceiling publicLimit : Int) (warm : Bool) :
    (String × Option Dynamic.Value) × Nat × Option Bool × Option Bool × List String :=
  let valid := 0 ≤ units && units ≤ 6
  let price := if series then rate * units * (units+1) / 2 + 2*units else rate*units+2
  let sourceOk := valid && price ≤ ceiling
  let phase := if !valid then "input" else if !sourceOk then "recursive-output"
    else if price > publicLimit then "public-output" else "ok"
  let entries := if !valid then 0 else if !series then 2 else if units == 0 then 1 else 2*units.toNat+2
  let before := if warm then ["enter","call"] ++ (if valid then ["after","exit"] else []) else []
  ((phase,if phase == "ok" then some (.integer price) else none),entries,
    if valid then some warm else none, some warm,
    before ++ ["enter","call"] ++ (if sourceOk then ["after","exit"] else []))

def run : IO Unit := do
  let mut count := 0
  for rate in [1,3] do
    let plan ← IO.ofExcept ((Callable.compile (schema rate) "Service").mapError reprStr)
    let generic ← IO.ofExcept ((generic plan.program).mapError reprStr)
    let broad ← IO.ofExcept ((registry 200).mapError reprStr)
    for series in [false,true] do
      for units in [-1,0,2,4,7] do
        for ceiling in [0,10,100] do
          let current ← IO.ofExcept ((registry ceiling).mapError reprStr)
          for publicLimit in [0,100] do
            for warm in [false,true] do
              let initial : Session plan.program := ⟨generic,⟨{},[],none⟩⟩
              let before := if warm then (call initial ⟨series,units,broad,100⟩).next else initial
              let result := call before ⟨series,units,current,publicLimit⟩
              let actual := (phase result.outcome, result.next.state.recursive.memo.entries.length,
                result.next.state.lastRead,result.reused,result.next.state.ledger)
              unless actual == control rate series units ceiling publicLimit warm do
                throw (IO.userError s!"recursive dispatch control {rate}/{series}/{units}/{ceiling}/{publicLimit}/{warm}: {repr actual}")
              count := count+1
  unless count == 240 do throw (IO.userError "case count")
  IO.println "RECURSIVE-DISPATCH-CONTROL-OK cases=240 complete-result memo-size both-hits retained-ledger"
#eval run
#print axioms RecursiveDispatch.callPacked_ok
#print axioms RecursiveDispatch.callPacked_error
#print axioms RecursiveDispatch.callPacked_state
#print axioms RecursiveDispatch.call_ok
#print axioms RecursiveDispatch.call_error
#print axioms RecursiveDispatch.call_state
#print axioms RecursiveDispatch.call_ledger
#print axioms RecursiveDispatch.Receipt.inputAccepted
#print axioms RecursiveDispatch.Receipt.outputAccepted
end LeanPoo.Tests.RecursiveDispatch
