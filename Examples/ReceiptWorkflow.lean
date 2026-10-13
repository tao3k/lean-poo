import LeanPoo.Functional.ReceiptAdmission
import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Examples.ReceiptWorkflow
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object Object.MethodCombination
open Functional.RecursiveDispatch
variable {program : CallableRecord.Self Dynamic.Value}
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

def registry (ceiling : Int) (maxUnits : Int := 6) : Except Dynamic.SchemaError Dynamic.Registry := do
  let registry : Dynamic.Registry := { descriptors := [
    ("Units", ⟨"Units", .integerRange 0 maxUnits, []⟩),
    ("Limit", ⟨"Limit", .integerRange 0 ceiling, []⟩),
    ("Input", ⟨"Input", .named "Units", []⟩),
    ("Output", ⟨"Output", .named "Limit", []⟩),
    ("Unit", ⟨"Unit", .unit, []⟩), ("Any", ⟨"Any", .top, []⟩)] }
  let (registry, _) ← Dynamic.DescriptorFactory.functionOf.call registry "Price"
    [.descriptor "Input", .descriptor "Output"]
  let (registry, _) ← Dynamic.DescriptorFactory.functionOf.call registry "Status"
    [.descriptor "Unit", .descriptor "Any"]
  return registry


structure Args (program : CallableRecord.Self Dynamic.Value) where
  units : Int
  registry : Dynamic.Registry
  saved : Option (Answer program) := none
  budget : Nat := 200
abbrev Action (program : CallableRecord.Self Dynamic.Value) :=
  EStateM (RecursiveDispatch.Error program) (RecursiveDispatch.State program (List String))
abbrev Fragment (program : CallableRecord.Self Dynamic.Value) := Contribution (Args program) (Action program) (Answer program)
abbrev Session (program : CallableRecord.Self Dynamic.Value) := DispatchSession (Args program) (Fragment program)
  (Answer program) (RecursiveDispatch.State program (List String)) (RecursiveDispatch.Error program)
def query (units : Int) : CatalogRequest := ⟨⟨"series","Price",none,false⟩,.integer units⟩
def mark (event : String) : Action program Unit := modify fun state => {state with ledger := state.ledger ++ [event]}
def generic (program : CallableRecord.Self Dynamic.Value) := do
  let initial : Multimethod (Args program) (Fragment program) (Action program (Answer program)) :=
    Multimethod.standard 2 (fun _ => [["Bulk","Base"],["Card","Channel"]])
      (fun _ => throw (RecursiveDispatch.Error.application (program := program) "missing"))
  let primary ← initial.contribute [.prototype "Base",.prototype "Channel"] (.primary (fun _ args => do
    mark "evaluate"
    callPacked args.registry (query args.units) args.budget 60))
  let after ← primary.contribute [.any,.any] (.after (fun _ => mark "after"))
  after.contribute [.any,.any] (.around (fun next args => do
    mark "enter"
    let answer ← match args.saved with
      | some saved =>
        if saved.request == query args.units then do
          mark "reuse"
          saved.revalidateMethod args.registry 60
        else next ()
      | none => next ()
    mark "exit"
    return answer))
def call (session : Session program) (args : Args program) := session.call
  (Codec.identity (Args program) (RecursiveDispatch.Error program)) (fun _ answer => .ok answer) args

def run : IO Unit := do
  let plan ← IO.ofExcept ((Object.Callable.compile (schema 3) "Service").mapError reprStr)
  let broad ← IO.ofExcept ((registry 200).mapError reprStr)
  let narrow ← IO.ofExcept ((registry 30).mapError reprStr)
  let constrained ← IO.ofExcept ((registry 200 3).mapError reprStr)
  let generic ← IO.ofExcept ((generic plan.program).mapError reprStr)
  let start : Session plan.program := ⟨generic,⟨{},[],some false⟩⟩
  let cold := call start {units := 4, registry := broad}
  let saved ← IO.ofExcept (cold.outcome.mapError reprStr)
  unless saved.value == .integer 38 do throw (IO.userError "source result")
  -- The recipient has no recursive cache and cannot evaluate with budget zero.
  let shortcut := call start {units := 4, registry := broad, saved := some saved, budget := 0}
  let admitted ← IO.ofExcept (shortcut.outcome.mapError reprStr)
  unless admitted.value == saved.value && admitted.receipt.reused == none &&
      shortcut.next.state.recursive.memo.entries.isEmpty && shortcut.next.state.lastRead == some false &&
      shortcut.next.state.ledger == ["enter","reuse","exit"] do throw (IO.userError "shortcut evaluated next")
  let refused := call shortcut.next {units := 4, registry := narrow, saved := some saved, budget := 0}
  unless refused.outcome matches .error (.method (.recursive (.boundary (.result _)))) do
    throw (IO.userError "stored output bypassed current descriptor")
  let inputRefused := call refused.next {units := 4, registry := constrained, saved := some saved, budget := 0}
  unless inputRefused.outcome matches .error (.method (.recursive (.boundary (.argument _)))) do
    throw (IO.userError "stored input bypassed current descriptor")
  let resumed := call inputRefused.next {units := 4, registry := broad, saved := some saved, budget := 0}
  unless resumed.outcome.isOk && resumed.next.state.recursive.memo.entries.isEmpty do
    throw (IO.userError "restored admission")
  let changed := call resumed.next {units := 2, registry := broad, saved := some saved}
  unless changed.outcome.toOption.map Answer.value == some (.integer 13) &&
      (changed.next.state.ledger.reverse.take 4).reverse == ["enter","evaluate","after","exit"] do
    throw (IO.userError "different request reused old answer")
  let (batch, retained) := start.callBatch (Codec.identity (Args plan.program) (RecursiveDispatch.Error plan.program))
    (fun _ answer => .ok answer)
    [{units := 4, registry := broad, saved := some saved, budget := 0},
     {units := 4, registry := narrow, saved := some saved, budget := 0},
     {units := 2, registry := broad}]
  unless batch matches .error (.method (.recursive (.boundary (.result _)))) do throw (IO.userError "batch refusal")
  unless retained.state.ledger == ["enter","reuse","exit","enter","reuse"] &&
      retained.state.recursive.memo.entries.isEmpty do throw (IO.userError "batch evaluated suffix")
  IO.println "RECEIPT-WORKFLOW-OK value=38 zero-budget empty-memo current-input/output refusal changed-request=13 batch-prefix"

#eval run
#print axioms ReAdmission.observed
#print axioms ReAdmission.outputAccepted
#print axioms Answer.revalidateMethod_state
#print axioms Answer.revalidate_noRead
end LeanPoo.Examples.ReceiptWorkflow
