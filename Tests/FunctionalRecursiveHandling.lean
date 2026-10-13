import LeanPoo.Functional.RecursiveHandling

namespace LeanPoo.Tests.FunctionalRecursiveHandling
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object.Callable

def schema (rate fee : Int) : Schema Dynamic.Value :=
  ⟨[("Root", ["Fee", "Rate"]), ("Fee", ["Base"]), ("Rate", ["Base"]), ("Base", [])],
    fun name =>
      if name == "Rate" then method "factor" (constant (.integer rate))
      else if name == "Fee" then method "quote" (modify fun _ value => match value with
        | .integer price => .integer (price + fee) | _ => .unit)
      else if name == "Base" then Prototype.composeAll [
        method "factor" (constant (.integer 0)),
        method "quote" (compute fun self argument => match argument with
          | .integer units => (self ⟨"factor", .unit⟩).map fun value => match value with
            | .integer rate => .integer (rate * units) | _ => .unit
          | _ => .error "units"),
        method "series" (compute fun self argument => match argument with
          | .integer units => if units ≤ 0 then .value (.integer 0) else
            (self ⟨"series", .integer (units - 1)⟩).bind fun left =>
            (self ⟨"quote", argument⟩).bind fun right =>
            match left, right with
            | .integer left, .integer right => .value (.integer (left + right))
            | _, _ => .error "prices"
          | _ => .error "units"),
        method "error" (fun _ _ _ => .error "unavailable"),
        method "loop" (compute fun self argument => self ⟨"loop", argument⟩)]
      else Prototype.identity, {}⟩

def registry (ceiling : Int) : Dynamic.Registry := { descriptors := [
  ("Price", ⟨"Price", .functionOf (.named "Units") (.named "Limit"), []⟩),
  ("Status", ⟨"Status", .functionOf .unit .top, []⟩),
  ("Units", ⟨"Units", .integerRange 0 5, []⟩),
  ("Limit", ⟨"Limit", .integerRange 0 ceiling, []⟩)] }
def query (name : String) (units : Int := 0) : CatalogRequest :=
  if name == "quote" || name == "series" then ⟨⟨name, "Price", none, false⟩, .integer units⟩
  else ⟨⟨name, "Status", none, false⟩, .unit⟩

inductive Outcome where
  | value (price : Int)
  | argument | result | source | exhausted | cycle | unexpected
  deriving BEq, Repr

def observe (outcome : Except (RecursiveFailure program) (CatalogAnswer program current)) : Outcome :=
  match outcome with
  | .ok answer => match answer.invocation.checked.value with
    | .integer price => .value price | _ => .unexpected
  | .error (.boundary (.argument _)) => .argument
  | .error (.boundary (.result _)) => .result
  | .error (.boundary (.source "unavailable")) => .source
  | .error (.evaluation _ .budgetExhausted) => .exhausted
  | .error (.evaluation _ (.cycle _ _)) => .cycle
  | _ => .unexpected

-- A direct price formula and a separate domain dependency schedule. Neither
-- executes Interaction trees, C3 declarations, the evaluator or descriptors.
structure Model where
  keys : List (Request Dynamic.Value) := []
  hits : Nat := 0
  misses : Nat := 0
  deriving BEq
def remember (model : Model) (key : Request Dynamic.Value) : Model := { model with keys := key :: model.keys }
def resolveFactor (model : Model) : Model :=
  let key : Request Dynamic.Value := ⟨"factor", .unit⟩
  if model.keys.contains key then {model with hits := model.hits + 1}
  else remember {model with misses := model.misses + 1} key
def resolveQuote (model : Model) (units : Int) : Model :=
  let key : Request Dynamic.Value := ⟨"quote", .integer units⟩
  if model.keys.contains key then {model with hits := model.hits + 1}
  else remember (resolveFactor {model with misses := model.misses + 1}) key
def resolveSeries (model : Model) : Nat → Model
  | 0 =>
    let key : Request Dynamic.Value := ⟨"series", .integer 0⟩
    if model.keys.contains key then {model with hits := model.hits + 1}
    else remember {model with misses := model.misses + 1} key
  | units + 1 =>
    let key : Request Dynamic.Value := ⟨"series", .integer (Int.ofNat (units + 1))⟩
    if model.keys.contains key then {model with hits := model.hits + 1}
    else remember (resolveQuote (resolveSeries {model with misses := model.misses + 1} units)
      (Int.ofNat (units + 1))) key

def control (rate fee ceiling : Int) (budget : Nat) (model : Model) (request : CatalogRequest) : Outcome × Model :=
  let name := request.slot.name
  let units := match request.argument with | .integer units => units | _ => 0
  let key : Request Dynamic.Value := ⟨name, request.argument⟩
  if (name == "quote" || name == "series") && (units < 0 || units > 5) then (.argument, model)
  else if name == "loop" then (.cycle, model)
  else if budget ≤ 1 && !model.keys.contains key then (.exhausted, model)
  else
    let next := if name == "quote" then resolveQuote model units
      else if name == "series" then resolveSeries model units.toNat
      else if model.keys.contains key then {model with hits := model.hits + 1}
      else remember {model with misses := model.misses + 1} key
    let price := if name == "quote" then rate * units + fee
      else rate * units * (units + 1) / 2 + fee * units
    (if name == "error" then .source else if price > ceiling then .result else .value price, next)

def modelOf (session : RecursiveSession program) : Model :=
  ⟨session.memo.entries.map (·.input), session.memo.statistics.hits, session.memo.statistics.misses⟩
def controlBatch (ceiling : Int) (model : Model) : List CatalogRequest → Except Outcome (List Int) × Model
  | [] => (.ok [], model)
  | request :: rest =>
    let (outcome, next) := control 3 2 ceiling 160 model request
    match outcome with
    | .value price =>
      let (remaining, final) := controlBatch ceiling next rest
      (remaining.map (price :: ·), final)
    | error => (.error error, next)
def batchObservation (result : Except (RecursiveFailure program) (List (CatalogAnswer program current))) :
    Except Outcome (List Int) :=
  match result with
  | .ok answers => .ok (answers.map (fun answer => match answer.invocation.checked.value with | .integer price => price | _ => -999))
  | .error error => .error (observe (.error error : Except (RecursiveFailure program) (CatalogAnswer program current)))
def sameBatch : Except Outcome (List Int) → Except Outcome (List Int) → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

def run : IO Unit := do
  let mut calls := 0
  for rate in ([1, 3, 5] : List Int) do
    for fee in ([0, 2] : List Int) do
      let plan ← IO.ofExcept ((compile (schema rate fee) "Root").mapError reprStr)
      for name in ["quote", "series"] do
        for units in ([-1, 0, 1, 2, 3, 5, 6] : List Int) do
          for warm in [false, true] do
            let empty : RecursiveSession plan.program := {}
            let request := query name units
            let session := if warm then (empty.callRequest (registry 1000) request 160 40).next else empty
            let initial := modelOf session
            for ceiling in ([0, 6, 20, 100] : List Int) do
              for budget in [1, 160] do
                let actual := session.callRequest (registry ceiling) request budget 40
                let (expected, next) := control rate fee ceiling budget initial request
                let marker := if units < 0 || units > 5 then none else some warm
                unless observe actual.outcome == expected && modelOf actual.next == next && actual.reused == marker do
                  throw (IO.userError s!"recursive control {calls}: rate={rate} fee={fee} name={name} units={units} warm={warm} budget={budget} expected={reprStr expected} actual={reprStr (observe actual.outcome)}")
                calls := calls + 1
  let plan ← IO.ofExcept ((compile (schema 3 2) "Root").mapError reprStr)
  let empty : RecursiveSession plan.program := {}
  let mut batches := 0
  for ceiling in ([0, 6, 20, 100] : List Int) do
    for warm in [false, true] do
      let session := if warm then (empty.callRequest (registry 1000) (query "series" 2) 160 40).next else empty
      for requests in [[], [query "quote" 0], [query "series" 2, query "quote" 1, query "series" 2],
          [query "series" 2, query "quote" 6, query "loop"],
          [query "series" 2, query "error", query "loop"],
          [query "series" 2, query "series" 4, query "quote" 1],
          [query "series" 1, query "loop", query "quote" 1]] do
        let (actual, retained) := session.callBatch (registry ceiling) requests 160 40
        let (expected, next) := controlBatch ceiling (modelOf session) requests
        unless sameBatch (batchObservation actual) expected && modelOf retained == next do
          throw (IO.userError s!"recursive batch/control {batches}")
        let resumed := retained.callRequest (registry 1000) (query "series" 3) 160 40
        let (continuation, final) := control 3 2 1000 160 next (query "series" 3)
        unless observe resumed.outcome == continuation && modelOf resumed.next == final do
          throw (IO.userError "recursive continuation/control")
        batches := batches + 1
  unless calls == 1344 && batches == 56 do throw (IO.userError "recursive coverage drift")
  IO.println s!"FUNCTIONAL-RECURSIVE-OK calls={calls} batches={batches} resumes={batches}"

#eval run

private partial def unforced (tree : Interaction (Request Dynamic.Value) Dynamic.Value Dynamic.Value) :
    Interaction (Request Dynamic.Value) Dynamic.Value Dynamic.Value := unforced tree
def guardedProgram : Prototype.CallableRecord.Self Dynamic.Value := fun request =>
  if request.name == "blocked" then unforced (.value .unit) else .value (.integer 3)
def guards : IO Unit := do
  let empty : RecursiveSession guardedProgram := {}
  let blocked := query "quote" 6
  let blocked := { blocked with slot := { blocked.slot with name := "blocked" } }
  let denied := empty.callRequest (registry 20) blocked 160 40
  unless observe denied.outcome == .argument && denied.reused == none && denied.next.memo.entries.isEmpty do
    throw (IO.userError "input gate forced divergent method")
  let missing := empty.callRequest ({} : Dynamic.Registry) {blocked with argument := .integer 1} 160 40
  unless missing.outcome matches .error (.boundary (.schema _)) do throw (IO.userError "catalog gate")
  let malformed : Dynamic.Registry := { descriptors := [("Price", ⟨"Price", .integer, []⟩)] }
  let invalid := empty.callRequest malformed {blocked with argument := .integer 1} 160 40
  unless invalid.outcome matches .error (.boundary (.signature _)) do throw (IO.userError "signature gate")
  let (result, retained) := empty.callBatch (registry 20)
    [query "quote" 1, blocked, { blocked with argument := .integer 1 }] 160 40
  unless result matches .error (.boundary (.argument _)) do throw (IO.userError "batch admission gate")
  unless retained.memo.entries.length == 1 && retained.memo.statistics.misses == 1 && empty.memo.entries.isEmpty do
    throw (IO.userError "batch lost prefix or forced divergent suffix")
  let inputFuel := retained.callRequest (registry 20) (query "quote" 1) 1 0
  unless observe inputFuel.outcome == .argument && inputFuel.reused == none &&
      inputFuel.next.memo.statistics == retained.memo.statistics do throw (IO.userError "input fuel gate")
  let outputFuel := retained.call (registry 20) ⟨"quote", .integerRange 0 5, .named "Limit"⟩ (.integer 1) 1 1
  unless outputFuel.outcome matches .error (.boundary (.result _)) do throw (IO.userError "output fuel gate")
  unless outputFuel.reused == some true && outputFuel.next.memo.statistics.hits == retained.memo.statistics.hits + 1 do
    throw (IO.userError "output refusal lost hot read")
  IO.println "RECURSIVE-GUARDS-OK unforced=3 skipped-suffix=1 input-fuel=1 output-fuel=1"

#eval guards
#print axioms RecursiveSession.call_input_error
#print axioms RecursiveSession.call_completed
#print axioms RecursiveSession.call_diagnostic
#print axioms RecursiveSession.admitted_values_agree
#print axioms RecursiveSession.callBatch_error_iff
#print axioms RecursiveSession.callBatch_requests
#print axioms RecursiveSession.callBatch_append
#print axioms CatalogInvocation.observed
#print axioms Validation.traverseState_project
end LeanPoo.Tests.FunctionalRecursiveHandling
