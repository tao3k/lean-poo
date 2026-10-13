import LeanPoo.Functional.RecursiveHandling

/-! A recursive configuration contains registered function references. Shared
method values remain program-bound while runtime schemas and identities are
revalidated in the current registry before publishing or serializing them. -/
namespace LeanPoo.Examples.RecursiveCatalog
open Functional Prototype Prototype.Recursive Prototype.CallableRecord Object.Callable

def schema : Schema Dynamic.Value :=
  ⟨[("Config", ["Scale", "Hooks"]), ("Scale", ["Base"]), ("Hooks", ["Base"]), ("Base", [])],
    fun name =>
      if name == "Scale" then method "head" (modify fun _ value => match value with
        | .integer value => .integer (2 * value) | _ => .unit)
      else if name == "Hooks" then method "callback" (constant (.function "alert"))
      else if name == "Base" then Prototype.composeAll [
        method "head" (compute fun _ argument => .value argument),
        method "callback" (constant (.function "notify")),
        method "chain" (compute fun self argument => match argument with
          | .integer count => if count ≤ 0 then .value .unit else
            (self ⟨"head", argument⟩).bind fun head =>
            (self ⟨"chain", .integer (count - 1)⟩).bind fun tail =>
            (self ⟨"callback", .unit⟩).bind fun callback =>
            .value (.object [("head", head), ("tail", tail), ("callback", callback)])
          | _ => .error "integer count required")]
      else Prototype.identity, {}⟩

def treeContract (ceiling : Int) : Dynamic.Contract :=
  .union .unit (.objectOf [("head", .integerRange 0 ceiling), ("tail", .named "Tree"),
    ("callback", .functionOf .integer .integer)])

def registry (ceiling : Int) (registered : Bool := true) : Except Dynamic.SchemaError Dynamic.Registry := do
  let registry : Dynamic.Registry := {
    descriptors := [("Count", ⟨"Count", .integerRange 0 5, []⟩),
      ("Input", ⟨"Input", .named "Count", []⟩), ("Output", ⟨"Output", .named "Tree", []⟩),
      ("Tree", ⟨"Tree", treeContract ceiling, []⟩)]
    functions := if registered then [("alert", Except.ok)] else [] }
  let (registry, _) ← Dynamic.DescriptorFactory.functionOf.call registry "Chain"
    [.descriptor "Input", .descriptor "Output"]
  return registry

def slot : Dynamic.SlotDescription := ⟨"chain", "Chain", none, false⟩
def query (count : Int) : CatalogRequest := ⟨slot, .integer count⟩
def expected : Nat → Dynamic.Value
  | 0 => .unit
  | count + 1 => .object [("head", .integer (2 * Int.ofNat (count + 1))),
      ("tail", expected count), ("callback", .function "alert")]

theorem serialized_source (plan : Plan Dynamic.Value) (current : Dynamic.Registry)
    (answer : CatalogAnswer plan.program current) (fuel : Nat)
    (bound : answer.invocation.checked.value.wireDepth ≤ fuel) :
    Dynamic.Value.decodeJson fuel answer.invocation.encodeJson = .ok answer.invocation.checked.value ∧
      ∃ depth, plan.call depth ⟨answer.request.slot.name, answer.request.argument⟩ =
        .value answer.invocation.checked.value :=
  ⟨answer.invocation.decode_encode fuel bound, answer.invocation.observed⟩

def memoState (session : RecursiveSession program) :=
  (session.memo.entries.map (·.input), session.memo.statistics)

def run : IO Unit := do
  let plan ← IO.ofExcept ((compile schema "Config").mapError reprStr)
  let broad ← IO.ofExcept ((registry 12).mapError reprStr)
  let narrow ← IO.ofExcept ((registry 3).mapError reprStr)
  let removed ← IO.ofExcept ((registry 12 false).mapError reprStr)
  let reflected ← IO.ofExcept ((Dynamic.SlotDescription.fromValue slot.describe).mapError reprStr)
  unless reflected == slot do throw (IO.userError "catalog reflection")
  let session : RecursiveSession plan.program := {}
  let first := session.callSlot broad reflected (.integer 3) 200 60
  let invocation ← IO.ofExcept (first.outcome.mapError reprStr)
  unless invocation.checked.value == expected 3 && first.next.memo.statistics.misses == 8 do
    throw (IO.userError "recursive configuration C3/sharing")
  let decoded ← IO.ofExcept ((Dynamic.Value.decodeJson invocation.checked.value.wireDepth
    invocation.encodeJson).mapError reprStr)
  unless decoded == expected 3 do throw (IO.userError "structural result wire")
  let staleIdentity := first.next.callSlot removed slot (.integer 3) 1 60
  unless staleIdentity.outcome matches .error (.boundary (.result (.admission (.unknownFunction "alert")))) do
    throw (IO.userError "warm nested references escaped current identity gate")
  unless staleIdentity.reused == some true && staleIdentity.next.memo.statistics.misses == first.next.memo.statistics.misses do
    throw (IO.userError "identity refusal recomputed or discarded memo")
  let staleSchema := staleIdentity.next.callSlot narrow slot (.integer 3) 1 60
  unless staleSchema.outcome matches .error (.boundary (.result _)) do throw (IO.userError "warm recursive schema gate")
  let inputNarrow : Dynamic.Registry := { broad with descriptors :=
    ("Count", ⟨"Count", .integerRange 0 1, []⟩) :: broad.descriptors }
  let inputRefused := staleSchema.next.callSlot inputNarrow slot (.integer 3) 1 60
  unless inputRefused.outcome matches .error (.boundary (.argument _)) do throw (IO.userError "warm input gate")
  unless inputRefused.reused == none && memoState inputRefused.next == memoState staleSchema.next do
    throw (IO.userError "input admission changed memo")
  let absent : Dynamic.Registry := { broad with descriptors := broad.descriptors.filter (fun entry => entry.1 != "Chain") }
  let missing := inputRefused.next.callSlot absent slot (.integer 3) 1 60
  unless missing.outcome matches .error (.boundary (.schema _)) do throw (IO.userError "current catalog identity")
  let malformed : Dynamic.Registry := { broad with descriptors := ("Chain", ⟨"Not a method", .integer, []⟩) :: broad.descriptors }
  let wrong := missing.next.callSlot malformed slot (.integer 3) 1 60
  unless wrong.outcome matches .error (.boundary (.signature .expectedFunctionContract)) do
    throw (IO.userError "current catalog signature")
  unless missing.reused == none && wrong.reused == none && memoState wrong.next == memoState inputRefused.next do
    throw (IO.userError "catalog refusal forced method")
  let restored := wrong.next.callSlot broad slot (.integer 3) 1 60
  unless restored.outcome.toOption.map (·.checked.value) == some (expected 3) && restored.reused == some true do
    throw (IO.userError "registry restoration did not re-admit shared value")
  let (result, retained) := session.callBatch narrow [query 1, query 2, query 0] 200 60
  unless result matches .error (.boundary (.result _)) do throw (IO.userError "recursive batch result gate")
  unless retained.memo.entries.length == 6 do throw (IO.userError "output refusal lost batch completion")
  let resume := retained.callRequest broad (query 2) 1 60
  unless resume.outcome.toOption.map (·.invocation.checked.value) == some (expected 2) && resume.reused == some true do
    throw (IO.userError "recursive batch resume")
  unless session.memo.entries.isEmpty do throw (IO.userError "original configuration session changed")
  IO.println "RECURSIVE-CATALOG-OK depth=3 misses=8 revalidated=5 restored=1 retained=6"

#eval run
#print axioms serialized_source
#print axioms CatalogInvocation.decode_encode
#print axioms RecursiveSession.callSlot_schema_error
#print axioms RecursiveSession.callSlot_signature_error
end LeanPoo.Examples.RecursiveCatalog
