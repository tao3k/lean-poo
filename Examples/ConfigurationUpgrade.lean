import LeanPoo.Functional.RecordEvolution

/-! Runtime configuration versions share one catalog for recognition, defaults,
reflection and generated updates. Migration explicitly carries public fields,
retires legacy fields and admits nested routes in the target catalog. -/
namespace LeanPoo.Examples.ConfigurationUpgrade
open Functional Functional.RecordEvolution Prototype.Dynamic

def catalog (capacity : Int) (callbacks : Bool := true) : Except SchemaError Registry := do
  let base : Registry := {
    descriptors := [("Text", ⟨"Text", .text, []⟩), ("Boolean", ⟨"Boolean", .boolean, []⟩),
      ("Action", ⟨"Action", .functionOf .integer .integer, []⟩)]
    functions := if callbacks then [("alert", Except.ok)] else [] }
  let (bounded, _) ← DescriptorFactory.integerRange.call base "Bound" [.integer 0, .integer capacity]
  let (route, _) ← DescriptorFactory.objectOf.call bounded "Route"
    [.object [("endpoint", .descriptor "Text"), ("weight", .descriptor "Bound"),
      ("hook", .descriptor "Action")]]
  let (routes, _) ← DescriptorFactory.listOf.call route "Routes" [.descriptor "Route"]
  return routes

def legacySchema : RecordSchema := ⟨"RoutingV1", [
  ⟨"owner", "Text", none, false⟩, ⟨"quota", "Bound", some (.integer 2), true⟩,
  ⟨"routes", "Routes", some (.list []), true⟩,
  ⟨"callback", "Action", some (.function "alert"), true⟩,
  ⟨"legacy", "Boolean", some (.boolean false), false⟩], true⟩

def currentSchema : RecordSchema := ⟨"RoutingV2", [
  ⟨"owner", "Text", none, false⟩, ⟨"budget", "Bound", some (.integer 2), true⟩,
  ⟨"routes", "Routes", some (.list []), true⟩,
  ⟨"callback", "Action", some (.function "alert"), true⟩,
  ⟨"policy", "Text", some (.text "balanced"), true⟩], true⟩

def upgrade : RecordMigration := ⟨legacySchema, currentSchema,
  [⟨"owner", "owner"⟩, ⟨"quota", "budget"⟩, ⟨"routes", "routes"⟩, ⟨"callback", "callback"⟩]⟩

def route (weight : Int) : Value := .object
  [("endpoint", .text "api"), ("weight", .integer weight), ("hook", .function "alert")]

/-- The actual field consumer receives the target descriptor's range proof.
The descriptor binding and slot list are explicit current-catalog premises. -/
theorem budget_bound (record : CheckedRecord currentSchema registry fuel)
    (descriptor : Descriptor) (resolved : currentSchema.descriptor registry = .ok descriptor)
    (slots : List (String × Contract)) (shape : descriptor.contract = .objectOf slots)
    (budget : ("budget", Contract.named "Bound") ∈ slots)
    (binding : registry.descriptor? "Bound" = some ⟨"Bound", .integerRange 0 capacity, []⟩)
    (found : record.value.slot? "budget" = some (.integer units)) : 0 ≤ units ∧ units ≤ capacity := by
  have member := record.slotAccepted descriptor resolved slots shape "budget" (.named "Bound") (.integer units) budget found
  cases member with
  | named registered admitted =>
    have same := Option.some.inj (registered.symm.trans binding)
    rw [same] at admitted
    cases admitted with | integerRange lower upper => exact ⟨lower, upper⟩

def run : IO Unit := do
  let old ← IO.ofExcept ((catalog 20).mapError reprStr)
  let current ← IO.ofExcept ((catalog 10).mapError reprStr)
  let removed ← IO.ofExcept ((catalog 10 false).mapError reprStr)
  let source ← IO.ofExcept ((construct legacySchema old 40
    [("owner", .text "team"), ("quota", .integer 6), ("routes", .list [route 4])]).mapError reprStr)
  let upgraded ← IO.ofExcept ((upgrade.checked old current 40 40 source.value).mapError reprStr)
  unless upgraded.value.slot? "budget" == some (.integer 6) &&
      upgraded.value.slot? "routes" == source.value.slot? "routes" &&
      upgraded.value.slot? "policy" == some (.text "balanced") &&
      upgraded.value.slot? "legacy" == none && source.value.slot? "quota" == some (.integer 6) do
    throw (IO.userError "migration rename/default/retirement")
  let restored ← IO.ofExcept ((RecordSchema.fromValue currentSchema.describe).mapError reprStr)
  unless restored == currentSchema do throw (IO.userError "schema metadata")
  let inspection ← IO.ofExcept ((restored.inspect current 40 upgraded.value).mapError reprStr)
  unless inspection matches .list [_, _, _, _, _] do throw (IO.userError "generated inspection")
  let text ← IO.ofExcept ((restored.encodeText current 40 upgraded.value).mapError reprStr)
  let decoded ← IO.ofExcept ((restored.decodeText current 40 text).mapError reprStr)
  unless decoded == upgraded.value do throw (IO.userError "schema wire tools")
  unless (upgrade.checked old removed 40 40 source.value) matches
      .error (.wire (.admission (.unknownFunction "alert"))) do
    throw (IO.userError "target nested identity admission")
  let narrow ← IO.ofExcept ((catalog 3).mapError reprStr)
  unless (upgrade.checked old narrow 40 40 source.value) matches .error (.wire (.rejected "RoutingV2")) do
    throw (IO.userError "target dependent bound")
  let overflow ← IO.ofExcept ((construct legacySchema old 40
    [("owner", .text "other"), ("quota", .integer 11)]).mapError reprStr)
  unless (upgrade.batch old current 40 40 [source.value, overflow.value, .unit]).toOption.isNone do
    throw (IO.userError "fleet migration published partial conversion")
  -- A default is admitted just like an explicitly supplied field.
  unless (construct currentSchema current 40 [("owner", .text "new")]).toOption.isSome &&
      (construct currentSchema removed 40 [("owner", .text "new")]) matches
        .error (.wire (.admission (.unknownFunction "alert"))) do
    throw (IO.userError "default identity admission")
  IO.println "CONFIGURATION-UPGRADE-OK rename=1 retired=1 default=balanced reflected=5 catalogs=current"

#eval run
#print axioms budget_bound
#print axioms RecordMigration.run_success_iff
#print axioms RecordMigration.batch_error_iff
#print axioms CheckedRecord.decode_encode
end LeanPoo.Examples.ConfigurationUpgrade
