import LeanPoo.Functional.RecursiveHandling

/-! C3 method wrapping, final-self recursion, shared subrequests and current
descriptor admission in an immutable, resumable billing session. -/
namespace LeanPoo.Examples.RecursiveBilling
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object.Callable

def schema (rate : Int) : Schema Dynamic.Value :=
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

def query (name : String) (units : Int) : CatalogRequest :=
  ⟨⟨name, "Price", none, false⟩, .integer units⟩
def status (name : String) : CatalogRequest := ⟨⟨name, "Status", none, false⟩, .unit⟩

def memoState (session : RecursiveSession program) :=
  (session.memo.entries.map (·.input), session.memo.statistics)

theorem admitted_source (plan : Plan Dynamic.Value) (registry : Dynamic.Registry)
    (answer : CatalogAnswer plan.program registry) :
    ∃ depth, plan.call depth ⟨answer.request.slot.name, answer.request.argument⟩ =
      .value answer.invocation.checked.value := answer.invocation.observed

theorem admitted_bound (current : Dynamic.Registry)
    (invocation : CatalogInvocation program current slot argument)
    (contract : invocation.signature.output = .named "Limit")
    (binding : current.descriptor? "Limit" = some ⟨"Limit", .integerRange 0 ceiling, []⟩)
    (value : invocation.checked.value = .integer price) : 0 ≤ price ∧ price ≤ ceiling := by
  have accepted := invocation.checked.outputAccepted
  rw [contract, value] at accepted
  cases accepted with
  | named found member =>
    have same := Option.some.inj (found.symm.trans binding)
    rw [same] at member
    cases member with | integerRange lower upper => exact ⟨lower, upper⟩

def run : IO Unit := do
  let plan ← IO.ofExcept ((compile (schema 3) "Service").mapError reprStr)
  let broad ← IO.ofExcept ((registry 200).mapError reprStr)
  let narrow ← IO.ofExcept ((registry 30).mapError reprStr)
  let session : RecursiveSession plan.program := {}
  let workload := [query "series" 4, query "quote" 2, query "series" 4]
  let (result, warm) := session.callBatch broad workload 200 60
  let answers ← IO.ofExcept (result.mapError reprStr)
  unless answers.map (·.invocation.checked.value) == [.integer 38, .integer 8, .integer 38] &&
      answers.map (·.request) == workload && warm.memo.statistics.misses == 10 do
    throw (IO.userError "recursive C3 quote/order/sharing")
  -- Input refusal skips the cyclic suffix and preserves the completed prefix.
  let (rejected, retained) := session.callBatch broad
    [query "series" 4, query "quote" 7, status "cycle"] 200 60
  unless rejected matches .error (.boundary (.argument _)) do throw (IO.userError "input gate")
  unless memoState retained == memoState (session.callRequest broad (query "series" 4) 200 60).next do
    throw (IO.userError "failed batch lost shared prefix")
  let refused := retained.callRequest narrow (query "series" 5) 200 60
  unless refused.outcome matches .error (.boundary (.result _)) do throw (IO.userError "output gate")
  unless refused.reused == some false && refused.next.memo.entries.length == 12 do
    throw (IO.userError "output refusal lost completed subrequests")
  -- This same completed result is now admitted, with only a hot top-level read.
  let resumed := refused.next.callRequest broad (query "series" 5) 1 60
  unless resumed.outcome.toOption.map (·.invocation.checked.value) == some (.integer 55) &&
      resumed.reused == some true && resumed.next.memo.statistics.misses == refused.next.memo.statistics.misses do
    throw (IO.userError "resume recomputed or reused old refusal")
  let source := resumed.next.callRequest broad (status "unavailable") 20 60
  let repeated := source.next.callRequest broad (status "unavailable") 1 60
  unless source.outcome matches .error (.boundary (.source "supplier unavailable")) do
    throw (IO.userError "source error confused with diagnostic")
  unless repeated.outcome matches .error (.boundary (.source "supplier unavailable")) do
    throw (IO.userError "source error memo")
  unless repeated.reused == some true && repeated.next.memo.entries.length == source.next.memo.entries.length do
    throw (IO.userError "source error sharing")
  let exhausted := repeated.next.callRequest broad (query "series" 6) 1 60
  unless exhausted.outcome matches .error (.evaluation _ .budgetExhausted) do
    throw (IO.userError "budget failure")
  unless memoState exhausted.next == memoState repeated.next do throw (IO.userError "incomplete memo publication")
  let cyclic := exhausted.next.callRequest broad (status "cycle") 20 60
  match cyclic.outcome with
  | .error (.evaluation request (.cycle path divergent)) =>
    have _ : Diverges plan.program request := divergent
    unless path == [⟨"cycle", .unit⟩, ⟨"cycle", .unit⟩] do throw (IO.userError "cycle path")
  | _ => throw (IO.userError "cycle not certified")
  unless memoState cyclic.next == memoState exhausted.next do throw (IO.userError "cycle changed memo")
  let continued := cyclic.next.callRequest broad (query "quote" 6) 30 60
  unless continued.outcome.toOption.map (·.invocation.checked.value) == some (.integer 20) do
    throw (IO.userError "diagnostic continuation")
  let revised ← IO.ofExcept ((compile (schema 4) "Service").mapError reprStr)
  let newSession : RecursiveSession revised.program := {}
  let changed := newSession.callRequest broad (query "series" 4) 200 60
  let old := warm.callRequest broad (query "series" 4) 1 60
  unless changed.outcome.toOption.map (·.invocation.checked.value) == some (.integer 48) &&
      old.outcome.toOption.map (·.invocation.checked.value) == some (.integer 38) &&
      changed.reused == some false && old.reused == some true && session.memo.entries.isEmpty do
    throw (IO.userError "immutable program revisions shared stale memo")
  IO.println "RECURSIVE-BILLING-OK series=38 refused=55 resumed=55 revised=48 misses=10"

#eval run
#print axioms admitted_source
#print axioms admitted_bound
#print axioms RecursiveSession.admitted_values_agree
#print axioms RecursiveSession.callBatch_requests
end LeanPoo.Examples.RecursiveBilling
