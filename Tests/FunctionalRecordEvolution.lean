import LeanPoo.Functional.RecordEvolution

namespace LeanPoo.Tests.FunctionalRecordEvolution
open Functional Functional.RecordEvolution Prototype.Dynamic

private instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq left right := match left, right with
    | .error left, .error right => left == right
    | .ok left, .ok right => left == right
    | _, _ => false

def catalog (capacity : Int) (registered : Bool := true) : Registry := {
  descriptors := [("Text", ⟨"Text", .text, []⟩), ("Boolean", ⟨"Boolean", .boolean, []⟩),
    ("Bound", ⟨"Bound", .integerRange 0 capacity, []⟩),
    ("Weights", ⟨"Weights", .listOf (.named "Bound"), []⟩),
    ("Action", ⟨"Action", .functionOf .integer .integer, []⟩)]
  functions := if registered then [("notify", Except.ok)] else [] }

def oldSchema : RecordSchema := ⟨"Old", [
  ⟨"owner", "Text", none, false⟩, ⟨"quota", "Bound", some (.integer 2), true⟩,
  ⟨"weights", "Weights", some (.list []), true⟩,
  ⟨"hook", "Action", some (.function "notify"), true⟩,
  ⟨"retired", "Boolean", some (.boolean false), false⟩], true⟩

def newSchema (validDefault : Bool) : RecordSchema := ⟨"New", [
  ⟨"owner", "Text", none, false⟩, ⟨"budget", "Bound", some (.integer 2), true⟩,
  ⟨"weights", "Weights", some (.list []), true⟩,
  ⟨"hook", "Action", some (.function "notify"), true⟩,
  ⟨"mode", "Text", some (if validDefault then .text "active" else .boolean false), true⟩], true⟩

def migration (validDefault carryBudget : Bool) : RecordMigration :=
  ⟨oldSchema, newSchema validDefault, [⟨"owner", "owner"⟩] ++
    (if carryBudget then [⟨"quota", "budget"⟩] else []) ++
    [⟨"weights", "weights"⟩, ⟨"hook", "hook"⟩]⟩

def oldValue (quota : Int) (weights : List Int) : Value := .object [
  ("owner", .text "team"), ("quota", .integer quota),
  ("weights", .list (weights.map Value.integer)), ("hook", .function "notify"),
  ("retired", .boolean false)]

def newValue (budget : Int) (weights : List Int) (mode : String := "active") : Value := .object [
  ("owner", .text "team"), ("budget", .integer budget),
  ("weights", .list (weights.map Value.integer)), ("hook", .function "notify"), ("mode", .text mode)]

-- A direct domain rule; no accepts, schema tools or migration functions run here.
def bounded (capacity : Int) (value : Int) : Bool := 0 ≤ value && value ≤ capacity
def admissible (capacity budget : Int) (weights : List Int) : Bool :=
  bounded capacity budget && weights.all (bounded capacity)

def expectedMigration (sourceCapacity targetCapacity quota : Int) (weights : List Int)
    (sourceRegistered targetRegistered validDefault carryBudget : Bool) : Except SchemaError Value :=
  if !sourceRegistered then .error (.wire (.admission (.unknownFunction "notify")))
  else if !admissible sourceCapacity quota weights then .error (.wire (.rejected "Old"))
  else if !targetRegistered then .error (.wire (.admission (.unknownFunction "notify")))
  else if !validDefault || !admissible targetCapacity (if carryBudget then quota else 2) weights then
    .error (.wire (.rejected "New"))
  else .ok (newValue (if carryBudget then quota else 2) weights)

-- A separate deployment model owns ordinary numeric/string fields, never Values.
structure Deployment where
  budget : Int
  weights : List Int
  mode : String := "active"
  deriving BEq

inductive Edit where
  | budget (value : Int)
  | weights (values : List Int)
  | mode (value : String)
  | owner | unknown | wrongBudget

def Edit.wire : Edit → String × Value
  | .budget value => ("budget", .integer value)
  | .weights values => ("weights", .list (values.map Value.integer))
  | .mode value => ("mode", .text value)
  | .owner => ("owner", .text "other")
  | .unknown => ("extra", .unit)
  | .wrongBudget => ("budget", .text "bad")

def Deployment.wire (state : Deployment) := newValue state.budget state.weights state.mode

def modelEdit (capacity : Int) (state : Deployment) : Edit → Except SchemaError Deployment
  | .budget value => if bounded capacity value then .ok { state with budget := value }
      else .error (.wire (.rejected "New"))
  | .weights values => if values.all (bounded capacity) then .ok { state with weights := values }
      else .error (.wire (.rejected "New"))
  | .mode value => .ok { state with mode := value }
  | .owner => .error (.readOnlySlot "owner")
  | .unknown => .error (.unknownSlot "extra")
  | .wrongBudget => .error (.wire (.rejected "New"))

def modelEdits (capacity : Int) (state : Deployment) : List Edit → Except SchemaError Deployment
  | [] => .ok state
  | edit :: rest => (modelEdit capacity state edit).bind fun next => modelEdits capacity next rest

def modelGroup (capacity : Int) (state : Deployment) (edits : List Edit) :
    Except SchemaError Deployment × Deployment :=
  let result := if admissible capacity state.budget state.weights then modelEdits capacity state edits
    else .error (.wire (.rejected "New"))
  (result, result.toOption.getD state)

def modelBatch (capacity : Int) (state : Deployment) : List (List Edit) →
    Except SchemaError (List Deployment) × Deployment
  | [] => (.ok [], state)
  | group :: rest =>
    let (result, next) := modelGroup capacity state group
    match result with
    | .error error => (.error error, next)
    | .ok output =>
      let (result, final) := modelBatch capacity next rest
      (result.map (output :: ·), final)

def schedules : List (List (List Edit)) := [[], [[]], [[.budget 0]],
  [[.budget 1, .budget 2], [.mode "canary"]],
  [[.mode "canary"], [.budget 1, .owner], [.mode "unreached"]],
  [[.mode "canary"], [.budget 9, .budget 0]],
  [[.budget 0, .budget 9]], [[.weights [1, 3]], [.mode "active"]],
  [[.unknown], [.budget 0]], [[.wrongBudget], [.mode "unreached"]],
  [[.mode "canary"], [.weights [-1]], [.owner]],
  [[.budget 0], [], [.weights []], [.mode "production"]]]

def observe (result : Except SchemaError (List (CheckedRecord schema registry fuel)) × Value) :=
  (result.1.map (List.map CheckedRecord.value), result.2)

def checkMigrations : IO Nat := do
  let mut count := 0
  for sourceCapacity in [2, 5] do
    for targetCapacity in [0, 2, 5] do
      for quota in [-1, 0, 1, 2, 3, 5, 6] do
        for weights in [[], [1], [1, 3]] do
          for sourceRegistered in [false, true] do
            for targetRegistered in [false, true] do
              for validDefault in [false, true] do
                for carryBudget in [false, true] do
                  let source := catalog sourceCapacity sourceRegistered
                  let target := catalog targetCapacity targetRegistered
                  let plan := migration validDefault carryBudget
                  let input := oldValue quota weights
                  let actual := (plan.checked source target 30 30 input).map CheckedRecord.value
                  let expected := expectedMigration sourceCapacity targetCapacity quota weights
                    sourceRegistered targetRegistered validDefault carryBudget
                  unless actual == expected do
                    throw (IO.userError s!"migration case={count}: actual={repr actual} expected={repr expected}")
                  match actual with
                  | .error _ => pure ()
                  | .ok output =>
                    unless output.slot? "owner" == input.slot? "owner" &&
                        output.slot? "weights" == input.slot? "weights" && output.slot? "retired" == none do
                      throw (IO.userError "migration public frame")
                    let wire ← IO.ofExcept ((plan.target.encodeText target 30 output).mapError reprStr)
                    unless (plan.target.decodeText target 30 wire).toOption == some output do
                      throw (IO.userError "target wire gate")
                  count := count + 1
  return count

def checkUpdates : IO Nat := do
  let mut count := 0
  for capacity in [2, 5] do
    for budget in [0, 1, 2, 4, 6] do
      for weights in [[], [1]] do
        for schedule in schedules do
          let registry := catalog capacity
          let schema := newSchema true
          let original : Deployment := ⟨budget, weights, "active"⟩
          let groups := schedule.map (List.map Edit.wire)
          let expected := modelBatch capacity original schedule
          let publicExpected := (expected.1.map (List.map Deployment.wire), expected.2.wire)
          let staged := updateBatch schema registry 30 original.wire groups
          unless observe staged == publicExpected do
            throw (IO.userError s!"staged case={count}: {repr (observe staged)} vs {repr publicExpected}")
          let atomic := updateAtomic schema registry 30 original.wire groups
          let atomicState := if expected.1.toOption.isNone then original.wire else expected.2.wire
          unless observe atomic == (publicExpected.1, atomicState) do
            throw (IO.userError "atomic publication")
          let repair := [[Edit.budget 0], [.mode "repair"]]
          let resumed := updateBatch schema registry 30 staged.2 (repair.map (List.map Edit.wire))
          let continuation := modelBatch capacity expected.2 repair
          unless observe resumed == (continuation.1.map (List.map Deployment.wire), continuation.2.wire) do
            throw (IO.userError "staged continuation")
          unless staged.2.slot? "owner" == some (.text "team") &&
              atomic.2.slot? "owner" == some (.text "team") do throw (IO.userError "read-only frame")
          count := count + 1
  return count

-- Later groups/edits cannot replace an earlier catalog or permission refusal.
def checkRefusals : IO Unit := do
  let registry := catalog 5
  let input := oldValue 2 []
  let plan := migration true true
  let absent : RecordMigration := { plan with fields := [⟨"missing", "budget"⟩] }
  unless absent.run registry registry 30 30 input == .error (.missingSlot "missing") do
    throw (IO.userError "missing projection")
  let duplicate : RecordMigration := { plan with fields := plan.fields ++ [⟨"quota", "budget"⟩] }
  unless duplicate.run registry registry 30 30 input == .error (.duplicateSlot "budget") do
    throw (IO.userError "duplicate target projection")
  unless plan.run registry registry 0 30 input == .error (.wire (.admission .budgetExhausted)) &&
      plan.run registry registry 30 0 input == .error (.wire (.admission .budgetExhausted)) do
    throw (IO.userError "independent source/target budgets")
  let target := catalog 5 false
  unless plan.run registry target 0 0 input == .error (.wire (.admission .budgetExhausted)) do
    throw (IO.userError "source refusal precedence")
  let current := newValue 2 []
  let refused := updateAtomic (newSchema true) registry 30 current
    [[("owner", .text "other")], [("extra", .unit)]]
  unless observe refused == (.error (.readOnlySlot "owner"), current) do
    throw (IO.userError "first group refusal")
  let missingType : Registry := { registry with descriptors := [] }
  let invalid := update (newSchema true) missingType 30 current [("owner", .text "other"), ("extra", .unit)]
  unless invalid.1.toOption.isNone && invalid.2 == current do throw (IO.userError "catalog refusal precedes edits")
  unless (construct (newSchema true) registry 30 [("owner", .text "team"), ("extra", .unit)]) matches
      .error (.unknownSlot "extra") do throw (IO.userError "sealed construction")
  unless (construct (newSchema true) registry 30 []).toOption.isNone do throw (IO.userError "missing mandatory default")

#eval do
  let migrations ← checkMigrations
  let batches ← checkUpdates
  checkRefusals
  IO.println s!"FUNCTIONAL-RECORD-EVOLUTION-OK migrations={migrations} batches={batches} continuations={batches} models=independent"

#print axioms RecordSchema.validate_membership
#print axioms RecordSchema.construct_validated
#print axioms RecordSchema.set_validated
#print axioms RecordSchema.patch_validated
#print axioms CheckedRecord.slotAccepted
#print axioms transferFields_targets
#print axioms RecordMigration.run_success_iff
#print axioms update_failure_state
#print axioms updateBatch_append
#print axioms updateBatch_invariant
#print axioms updateAtomic_invariant
end LeanPoo.Tests.FunctionalRecordEvolution
