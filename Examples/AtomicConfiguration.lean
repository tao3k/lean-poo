import LeanPoo.Functional.RecordEvolution

/-! A staged deployment changes several writable fields. Each group is atomic;
ordinary batches retain completed groups, while atomic publication retains the
initial version on any refusal. Continuation uses the explicitly returned value. -/
namespace LeanPoo.Examples.AtomicConfiguration
open Functional Functional.RecordEvolution Prototype.Dynamic

def catalog (capacity : Int) : Except SchemaError Registry := do
  let base : Registry := { descriptors := [("Text", ⟨"Text", .text, []⟩)] }
  let (bounded, _) ← DescriptorFactory.integerRange.call base "Bound" [.integer 0, .integer capacity]
  let (routes, _) ← DescriptorFactory.listOf.call bounded "Routes" [.descriptor "Bound"]
  return routes

def currentSchema : RecordSchema := ⟨"Deployment", [
  ⟨"owner", "Text", none, false⟩, ⟨"budget", "Bound", some (.integer 2), true⟩,
  ⟨"routes", "Routes", some (.list []), true⟩,
  ⟨"policy", "Text", some (.text "balanced"), true⟩], true⟩

def run : IO Unit := do
  let registry ← IO.ofExcept ((catalog 10).mapError reprStr)
  let original ← IO.ofExcept ((construct currentSchema registry 40
    [("owner", .text "team"), ("budget", .integer 6)]).mapError reprStr)
  let groups := [[("budget", Value.integer 8), ("policy", .text "canary")],
    [("budget", .integer 9), ("owner", .text "intruder")],
    [("policy", .text "production")]]
  let (outcome, retained) := updateBatch currentSchema registry 40 original.value groups
  let (atomic, rolledBack) := updateAtomic currentSchema registry 40 original.value groups
  unless outcome matches .error (.readOnlySlot "owner") do throw (IO.userError "staged refusal")
  unless atomic matches .error (.readOnlySlot "owner") do throw (IO.userError "atomic refusal")
  unless retained.slot? "budget" == some (.integer 8) &&
      retained.slot? "policy" == some (.text "canary") &&
      retained.slot? "owner" == some (.text "team") && rolledBack == original.value do
    throw (IO.userError "group or publication rollback")
  let (resumed, final) := updateBatch currentSchema registry 40 retained
    [[("budget", .integer 9)], [("policy", .text "production")]]
  unless resumed.toOption.map List.length == some 2 && final.slot? "budget" == some (.integer 9) &&
      final.slot? "policy" == some (.text "production") do throw (IO.userError "staged continuation")
  let (committed, published) := updateAtomic currentSchema registry 40 original.value
    [[("budget", .integer 7), ("budget", .integer 9)], [("routes", .list [.integer 5])]]
  unless committed.toOption.map List.length == some 2 && published.slot? "budget" == some (.integer 9) &&
      published.slot? "routes" == some (.list [.integer 5]) do throw (IO.userError "ordered atomic commit")
  -- Reusing a value under a narrowed catalog checks the old value first.
  let narrowed ← IO.ofExcept ((catalog 3).mapError reprStr)
  let (refused, unchanged) := update currentSchema narrowed 40 final [("budget", .integer 2)]
  unless refused matches .error (.wire (.rejected "Deployment")) do throw (IO.userError "current base admission")
  unless unchanged == final do throw (IO.userError "base refusal published repair")
  let cell ← IO.mkRef original.value
  let (mutableResult, next) := updateAtomic currentSchema registry 40 (← cell.get) groups
  cell.set next
  unless mutableResult.toOption.isNone && (← cell.get) == original.value do
    throw (IO.userError "mutable adapter changed publication semantics")
  IO.println "ATOMIC-CONFIGURATION-OK retainedBudget=8 rollbackBudget=6 resumedBudget=9 groups=atomic"

/-- The concrete adapters can install exactly the state returned by these pure
laws. They do not establish arbitrary external-effect rollback. -/
theorem publication_retains_admission (record : CheckedRecord currentSchema registry fuel)
    (groups : List (List (String × Value))) :
    currentSchema.validate registry fuel (updateAtomic currentSchema registry fuel record.value groups).2 =
      .ok (updateAtomic currentSchema registry fuel record.value groups).2 :=
  updateAtomic_invariant currentSchema registry fuel record.value groups record.validated

#eval run
#print axioms publication_retains_admission
#print axioms updateBatch_error_iff
#print axioms updateAtomic_error
#print axioms updateAtomic_success
end LeanPoo.Examples.AtomicConfiguration
