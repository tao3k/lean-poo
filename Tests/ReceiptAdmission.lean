import LeanPoo.Functional.ReceiptAdmission
import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Tests.ReceiptAdmission
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

def query (units : Int) : CatalogRequest := ⟨⟨"series","Price",none,false⟩,.integer units⟩
def variant (registry : Dynamic.Registry) (kind : Nat) : Dynamic.Registry :=
  { registry with
    descriptors := registry.descriptors.filterMap fun entry =>
      if (kind == 1 && entry.1 == "Price") || (kind == 3 && entry.1 == "Units") ||
          (kind == 4 && entry.1 == "Limit") then none
      else if kind == 2 && entry.1 == "Price" then some ("Price",⟨"Price",.top,[]⟩)
      else some entry }
def phase (outcome : Except Object.Callable.InvokeError A) : String :=
  match outcome with
  | .ok _ => "ok"
  | .error (.schema _) => "schema"
  | .error (.signature _) => "signature"
  | .error (.argument _) => "input"
  | .error (.result _) => "output"
  | _ => "unexpected"
def control (kind fuel : Nat) (units maximum price ceiling : Int) : String :=
  if kind == 1 then "schema" else if kind == 2 then "signature"
  else if fuel < 3 || kind == 3 || units > maximum then "input"
  else if kind == 4 || price > ceiling then "output" else "ok"
def memoState (session : RecursiveSession program) := (session.memo.entries.map (·.input),session.memo.statistics)
def run : IO Unit := do
  let mut count := 0
  for rate in [1,3] do
    let plan ← IO.ofExcept ((Object.Callable.compile (schema rate) "Service").mapError reprStr)
    let broad ← IO.ofExcept ((registry 200).mapError reprStr)
    for units in [0,2,4,6] do
      let originalCall := ({} : RecursiveSession plan.program).callSlot broad (query units).slot (query units).argument 200 60
      let originalInvocation ← IO.ofExcept (originalCall.outcome.mapError reprStr)
      let original : Answer plan.program := ⟨broad,query units,⟨originalInvocation,originalCall.reused⟩⟩
      let price := rate * units * (units + 1) / 2 + 2 * units
      unless original.value == .integer price do throw (IO.userError "independent recursive price")
      for kind in [0,1,2,3,4] do
        for maximum in [0,3,6] do
          for ceiling in [0,10,200] do
            let catalog ← IO.ofExcept ((registry ceiling maximum).mapError reprStr)
            let current := variant catalog kind
            for fuel in [0,1,60] do
              let result := original.revalidate current fuel
              let expected := control kind fuel units maximum price ceiling
              unless phase result == expected do
                throw (IO.userError s!"receipt control mismatch {rate}/{units}/{kind}/{maximum}/{ceiling}/{fuel}: {phase result} != {expected}")
              match result with
              | .ok admitted =>
                unless admitted.answer.value == .integer price && admitted.answer.request == query units &&
                    admitted.receipt.reused == none do throw (IO.userError "receipt relabeled source")
              | .error _ => pure ()
              -- Nonempty memo, statistics and an existing read marker must all survive.
              let state : RecursiveDispatch.State plan.program (List String) :=
                ⟨originalCall.next,["prefix"],some true⟩
              let methodResult := (original.revalidateMethod current fuel).run state
              let retained := returnedState methodResult
              unless memoState retained.recursive == memoState state.recursive &&
                  retained.ledger == state.ledger && retained.lastRead == state.lastRead do
                throw (IO.userError "receipt admission changed retained state")
              match methodResult with
              | .ok answer _ => unless expected == "ok" && answer.value == .integer price do
                  throw (IO.userError "method success control")
              | .error (.recursive (.boundary error)) _ =>
                unless phase (.error error : Except Object.Callable.InvokeError Unit) == expected do
                  throw (IO.userError "method failure control")
              | _ => throw (IO.userError "unexpected method failure")
              count := count + 1
  unless count == 1080 do throw (IO.userError "receipt control inventory")
  IO.println s!"RECEIPT-ADMISSION-OK cases={count} independent-prices catalog/signature/input/output precedence state-preservation"
#eval run
#print axioms Answer.revalidate_schema_error
#print axioms Answer.revalidate_signature_error
#print axioms Answer.revalidate_argument_error
#print axioms Answer.revalidate_result_error
#print axioms Answer.revalidateMethod_state
end LeanPoo.Tests.ReceiptAdmission
