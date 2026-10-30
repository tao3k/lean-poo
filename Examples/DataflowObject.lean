import LeanPoo.Object.Dataflow
import LeanPoo.Functional.ObjectContractRefinement
import Lean

namespace DataflowObjectExample
open LeanPoo LeanPoo.Object.Dataflow

inductive Key where
  | seed | result | other
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Value (_ : Key) := Nat
abbrev Object := Instance Key Value
private def defineObject (name : String) (program : Builder Key Value PUnit) : Except (Error Key) Object :=
  define name program

private def program : Builder Key Value PUnit := do
  Builder.value .seed 1
  Builder.derived .result ((· + 1) <$> Expr.need .seed)

private def checks : Bool :=
  match defineObject "Base" program with
  | .error _ => false
  | .ok parent =>
    match parent.extendWith "Child" (Builder.value .seed 5) with
    | .error _ => false
    | .ok child =>
      parent.read .seed == some 1 && parent.read .result == some 2 &&
      child.read .seed == some 5 && child.read .result == some 6 &&
      (child.read .other).isNone &&
      parent.slotNames == [.seed,.result] && child.slotNames == [.seed,.result]

private def missing : Bool :=
  match defineObject "Missing" (Builder.derived .result ((· + 1) <$> Expr.need .seed)) with
  | .error _ => false
  | .ok object => (object.read .result).isNone && (object.read .seed).isNone &&
      object.slotNames == [.result]

private def cycle : Bool :=
  (defineObject "Cycle" (do
    Builder.derived .seed (Expr.need .result)
    Builder.derived .result (Expr.need .seed))).toOption.isNone

private def pruned : Bool :=
  let broken : Declaration Key Value := Builder.build do
    Builder.field .result (.replace (.opaque fun _ _ => .error (.source "must not execute")))
  let fixed : Declaration Key Value := Builder.build (Builder.value .result 42)
  let source := Source.empty.add {name := "Broken"} broken
    |>.add {name := "Replaced",parentOrders := [["Broken"]]} fixed
  match Template.prepare source "Replaced" with
  | .error _ => false
  | .ok ready => match ready.instantiate with
    | .error _ => false
    | .ok object => object.read .result == some 42

private def topologyFirst : Bool :=
  let source : Source Key Value := Source.empty.add
    {name := "Bad",parentOrders := [["Absent"]]} (Builder.build program)
  match Template.prepare source "Bad" with
  | .error (.topology _) => true
  | _ => false

private def actualEvaluations : Bool :=
  match prepareDefinition (Key := Key) (Value := Value) "Counts" program with
  | .error _ => false
  | .ok ready => match ready.build with
    | .error _ => false
    | .ok (object,evaluated) => evaluated.length == 2 &&
      evaluated.count .seed == 1 && evaluated.count .result == 1 &&
      object.read .result == some 2

private def strictChecks : Bool :=
  let duplicate := defineStrict (Key := Key) (Value := Value) "Duplicate" do
    StrictBuilder.value .seed 1
    StrictBuilder.value .seed 2
  match duplicate with
  | .error (.duplicate (.slot .seed)) =>
    match defineStrict (Key := Key) (Value := Value) "Defaults" (do
      StrictBuilder.default .seed 1
      StrictBuilder.default .seed 2) with
    | .error (.duplicate (.default .seed)) => true
    | _ => false
  | _ => false

private def joinedInheritance : Bool :=
  let parent := defineStrict (Key := Key) (Value := Value) "First" do
    StrictBuilder.default .seed 10
    StrictBuilder.value .other 2
    StrictBuilder.derived .result ((· + 1) <$> Expr.need .seed)
  let amendment := defineStrict (Key := Key) (Value := Value) "Second" do
    StrictBuilder.modifyInherited .seed (Option.map (· + 5))
  match parent,amendment with
  | .ok first,.ok second =>
    match first.defineStrictFrom "Joined" [second] (StrictBuilder.value .other 9) with
    | .ok joined => joined.read .seed == some 15 && joined.read .result == some 16 &&
        first.read .seed == some 10 && first.read .result == some 11 &&
        joined.read .other == some 9
    | _ => false
  | _,_ => false

private def sharedDependency : Bool :=
  match prepareDefinition (Key := Key) (Value := Value) "Shared" (do
    Builder.value .seed 10
    Builder.derived .other ((· + 2) <$> Expr.need .seed)
    Builder.derived .result ((· + ·) <$> Expr.need .seed <*> Expr.need .other)) with
  | .error _ => false
  | .ok ready => match ready.build with
    | .error _ => false
    | .ok (object,evaluated) => object.read .result == some 22 &&
        evaluated.count .seed == 1 && evaluated.count .other == 1 && evaluated.count .result == 1

private def changedEdges : Bool :=
  match prepareDefinition (Key := Key) (Value := Value) "BeforeEdges" (do
    Builder.value .seed 10
    Builder.value .other 40
    Builder.derived .result ((· + 1) <$> Expr.need .seed)) with
  | .error _ => false
  | .ok prior =>
    let source := prior.source.add {name := "AfterEdges",parentOrders := [["BeforeEdges"]]}
      (Builder.build (Builder.derived .result ((· + 1) <$> Expr.need .other)))
    match Template.prepare source "AfterEdges" (some prior) with
    | .error _ => false
    | .ok ready =>
      match ready.instantiate with
      | .error _ => false
      | .ok object => (prior.rebaseSchedule? ready.graph).isNone && object.read .result == some 41

private def scheduleRevision : Bool :=
  match defineObject "ScheduledBase" program with
  | .error _ => false
  | .ok parent =>
    let same := parent.template.source.add
      {name := "SameEdges",parentOrders := [["ScheduledBase"]]}
      (Builder.build (Builder.value .seed 20))
    match Template.prepare same "SameEdges" (some parent.template) with
    | .error _ => false
    | .ok ready =>
      let reused := ready.rebaseSchedule? ready.graph
      match ready.instantiate with
      | .error _ => false
      | .ok object => reused.isSome && object.read .result == some 21 && parent.read .result == some 2

-- The structural contract accepts an actual source-bound executable object.
private def contract : LeanPoo.Functional.ObjectContract.Contract Object Key Unit String where
  view := {
    isObject := fun _ => true
    prototype := fun _ => true
    names := Instance.slotNames
    lookup := fun object key => (object.read key).map fun _ => () }
  fields := [.seed,.result].map fun key => {name := key,check := fun _ _ => []}
  strict := true
  constraints := []
  obligations := fun object path =>
    match object.read .seed,object.read .result with
    | some seed,some result => if result == seed + 1 then [] else [.rejected path "self mismatch"]
    | _,_ => [.rejected path "missing projection"]
  validInventory := Or.inl rfl

private def contractChecks : Bool :=
  match defineObject "Contract" program with
  | .error _ => false
  | .ok object => (LeanPoo.Functional.ObjectContract.diagnose contract object []).isEmpty

private def contractRefusal : Bool :=
  match defineObject "Forged" (do
    Builder.value .seed 1
    Builder.value .result 99) with
  | .error _ => false
  | .ok object => !(LeanPoo.Functional.ObjectContract.diagnose contract object []).isEmpty

open Lean in
run_cmd do
  for declaration in [``Instance.reference,``Instance.read_reference,``Instance.slotNames_exact,
      ``LeanPoo.Functional.ConstructionCache.Execution.compile,
      ``LeanPoo.Functional.ConstructionCache.Cache.reference,
      ``LeanPoo.Functional.ConstructionCache.Partial.step_reused_builder_independent] do
    for dependency in ← collectAxioms declaration do
      unless ["propext","Classical.choice","Quot.sound"].contains dependency.toString do
        throwError "Materialized object axiom boundary changed: {declaration}: {dependency}"
  logInfo "DATAFLOW-OBJECT-LAWS-OK actual closure, read and inventory"

def run : IO Unit := do
  for (name,passed) in [("current-self-and-parent-retirement",checks),("missing-input",missing),
      ("cycle-refusal",cycle),("dead-parent-pruned",pruned),("topology-error-order",topologyFirst),
      ("one-evaluation-per-field",actualEvaluations),("typed-contract",contractChecks),("strict-duplicates",strictChecks),
      ("disjoint-families-delayed-super",joinedInheritance),("schedule-revision",scheduleRevision),
      ("shared-dependency-evaluated-once",sharedDependency),("changed-edges-reject-reuse",changedEdges),
      ("contract-rejects-forged-projection",contractRefusal)] do
    unless passed do throw (IO.userError s!"dataflow object failed: {name}")
    IO.println s!"DATAFLOW-OBJECT-OK {name}"
end DataflowObjectExample

def main : IO Unit := DataflowObjectExample.run
