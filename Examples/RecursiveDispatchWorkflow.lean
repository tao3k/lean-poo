import LeanPoo.Functional.RecursiveDispatch
import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Examples.RecursiveDispatchWorkflow
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object Object.MethodCombination
open Functional.RecursiveDispatch
variable {program : CallableRecord.Self Dynamic.Value} {current : Dynamic.Registry} {request : CatalogRequest}
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
  mode : String
  channel : String
  units : Int
  registry : Dynamic.Registry
  limit : Int := 200
  budget : Nat := 200
  recover : Bool := false
  label : String := "request"
abbrev Ledger := List String
abbrev Action (program : Self Dynamic.Value) := EStateM (RecursiveDispatch.Error program) (RecursiveDispatch.State program Ledger)
abbrev Fragment (program : Self Dynamic.Value) := Contribution Args (Action program) (Answer program)
abbrev Session (program : Self Dynamic.Value) := DispatchSession Args (Fragment program) (Answer program)
  (RecursiveDispatch.State program Ledger) (RecursiveDispatch.Error program)
def query (name : String) (units : Int) : CatalogRequest := ⟨⟨name,"Price",none,false⟩,.integer units⟩
def memoState (session : RecursiveSession program) := (session.memo.entries.map (·.input),session.memo.statistics)

def mark (event : String) : Action program Unit := modify fun state => { state with ledger := state.ledger ++ [event] }
def source (name : String) (args : Args) : Action program (Answer program) := do
  mark name
  callPacked args.registry (query name args.units) args.budget 60

def generic (program : Self Dynamic.Value) : Except MultimethodError (Multimethod Args (Fragment program) (Action program (Answer program))) := do
  let initial : Multimethod Args (Fragment program) (Action program (Answer program)) := Multimethod.standard 2
    (fun args : Args => [[args.mode,"Base"],[args.channel,"Channel"]])
    (fun _ => throw (.application "missing method"))
  let basic ← initial.contribute [.prototype "Base",.prototype "Channel"]
    (.primary (fun _ args => source "quote" args))
  let bulk ← basic.contribute [.prototype "Bulk",.prototype "Channel"]
    (.primary (fun _ args => source "series" args))
  let cyclic ← bulk.contribute [.prototype "Cycle",.prototype "Channel"]
    (.primary (fun _ args => source "cycle" args))
  let offline ← cyclic.registerWhen [.prototype "Bulk",.prototype "Card"] (·.units > 4)
    (.primary (fun _ args => source "unavailable" args))
  let audited ← offline.contribute [.any,.any] (.around (fun next args => do
    mark ("enter:"++args.label)
    let answer ← if args.recover then
      DispatchSession.recoverMethod (next ()) (fun _ => source "quote" args)
    else next ()
    mark ("exit:"++args.label)
    return answer))
  audited.contribute [.any,.any] (.after (fun _ => mark "after"))

structure Approved (program : Self Dynamic.Value) where
  answer : Answer program
  limit : Int
  bounded : ∀ value, answer.receipt.invocation.checked.value = .integer value → value ≤ limit

def admit (args : Args) (answer : Answer program) : Except (RecursiveDispatch.Error program) (Approved program) :=
  match value : answer.receipt.invocation.checked.value with
  | .integer price => if bound : price ≤ args.limit then
      .ok ⟨answer,args.limit,by intro other same; have eq := Dynamic.Value.integer.inj (value.symm.trans same); omega⟩
    else .error (.application "public ceiling")
  | _ => .error (.application "integer price required")

def call (session : Session program) (args : Args) := session.call
  (Codec.identity Args (RecursiveDispatch.Error program)) admit args

def run : IO Unit := do
  let plan ← IO.ofExcept ((Object.Callable.compile (schema 3) "Service").mapError reprStr)
  let broad ← IO.ofExcept ((registry 200).mapError reprStr)
  let narrow ← IO.ofExcept ((registry 30).mapError reprStr)
  let generic ← IO.ofExcept ((generic plan.program).mapError reprStr)
  let start : Session plan.program := ⟨generic, ⟨{},[],none⟩⟩
  let args : Args := { mode := "Bulk", channel := "Card", units := 4, registry := broad }
  let cold := call start args
  let first ← IO.ofExcept (cold.outcome.mapError reprStr)
  unless first.answer.receipt.invocation.checked.value == .integer 38 && cold.reused == some false &&
      cold.next.state.lastRead == some false do throw (IO.userError "cold recursive dispatch")
  let hot := call cold.next {args with label := "hot", budget := 1}
  unless hot.outcome.isOk && hot.reused == some true && hot.next.state.lastRead == some true do
    throw (IO.userError "two warm caches")
  let refused := call hot.next {args with registry := narrow, label := "narrow"}
  unless refused.outcome matches .error (.method (.recursive (.boundary (.result _)))) do
    throw (IO.userError "hot output bypassed current registry")
  let resumed := call refused.next {args with label := "resume", budget := 1}
  unless resumed.outcome.isOk && resumed.next.state.lastRead == some true do throw (IO.userError "re-admission")
  let ceiling := call resumed.next {args with limit := 30, label := "public"}
  unless ceiling.outcome matches .error (.output (.application "public ceiling")) do
    throw (IO.userError "outer admission")
  let recovered := call ceiling.next {args with units := 5, recover := true, label := "fallback"}
  let recoveredAnswer ← IO.ofExcept (recovered.outcome.mapError reprStr)
  unless recoveredAnswer.answer.request.slot.name == "quote" &&
      recoveredAnswer.answer.receipt.invocation.checked.value == .integer 17 do throw (IO.userError "recovery source identity")
  let (batched, retained) := recovered.next.callBatch (Codec.identity Args (RecursiveDispatch.Error plan.program)) admit
    [{args with units := 2}, {args with units := 7}, {args with label := "skipped"}]
  unless batched matches .error (.method (.recursive (.boundary (.argument _)))) do throw (IO.userError "batch input refusal")
  unless !(retained.state.ledger.contains "enter:skipped") do throw (IO.userError "batch suffix executed")
  let exhausted := call retained {args with units := 6, channel := "Bank", budget := 1}
  unless exhausted.outcome matches .error (.method (.recursive (.evaluation _ .budgetExhausted))) do
    throw (IO.userError "budget diagnostic")
  unless memoState exhausted.next.state.recursive == memoState retained.state.recursive do
    throw (IO.userError "incomplete publication")
  let cyclic := call exhausted.next {args with mode := "Cycle"}
  match cyclic.outcome with
  | .error (.method (.recursive (.evaluation request (.cycle _ divergent)))) =>
    have _ : Diverges plan.program request := divergent
    pure ()
  | _ => throw (IO.userError "certified cycle lost in dispatch")
  let continued := call cyclic.next {args with units := 6, channel := "Bank"}
  unless continued.outcome.toOption.map (fun a => a.answer.receipt.invocation.checked.value) == some (.integer 75) do
    throw (IO.userError "resume after diagnostics")
  IO.println "RECURSIVE-DISPATCH-WORKFLOW-OK price=38 fallback=17 hot-current-admission retained-errors batch-prefix budget cycle continuation"

#eval run

theorem admitted_observation (receipt : Receipt program current request) :
    ∃ depth, solve program depth ⟨request.slot.name,request.argument⟩ = .value receipt.invocation.checked.value := receipt.observed
#print axioms RecursiveDispatch.call_state
#print axioms RecursiveDispatch.Receipt.observed
#print axioms DispatchSession.call_observation
#print axioms DispatchSession.callBatch_cacheSound
end LeanPoo.Examples.RecursiveDispatchWorkflow
