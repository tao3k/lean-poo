import LeanPoo.Functional.ComputationBatch
import LeanPoo.Functional.AnalyzedMigration

/-! A finite workload combines required limits, optional priority and an absent
legacy method. Graph extension and edits must preserve both capability policy and
computed observations; affected batches need new admission before publication. -/
namespace LeanPoo.Examples.IncrementalWorkflow
open Functional Requirements

inductive Capability where
  | capacity | priority | legacy | label
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr
instance : Hashable Capability where hash key := hash (reprStr key)

def Value (context : Nat) : Capability → Type
  | .capacity => {bound : Nat // bound ≤ context + 10}
  | .priority => Bool
  | .legacy => Nat
  | .label => String

abbrev Plan (context : Nat) := {amounts : List Nat // amounts.sum ≤ context + 10}

def job (cost : Nat) : Computation Nat Capability Value (fun _ => Nat) :=
  .validate (.both (.need .capacity (fun _ bound => bound))
    (.read .priority (fun _ value => value.getD false)) (fun _ bound priority => (bound, priority)))
    (fun context (bound, priority) =>
      let amount := context + cost - (cond (show Bool from priority) 1 0)
      if amount ≤ bound.val then .ok amount else .error "job outside capacity")

def workload : Computation Nat Capability Value Plan :=
  .validate (.both (Computation.traverse [2, 3] job) (.deny .legacy (fun _ => ()))
    (fun _ amounts _ => amounts))
    (fun context amounts => if allowed : amounts.sum ≤ context + 10 then .ok ⟨amounts, allowed⟩
      else .error "combined workload outside capacity")

def oldGraph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["Base"]]}, {name := "Base"}]}
def extendedGraph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["Plugin", "Base"]]},
  {name := "Plugin"}, {name := "Base"}]}
def cyclicGraph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["Base"]]},
  {name := "Base", parentOrders := [["Root"]]}]}

def providers (name : String) : Provider Nat Capability Value := fun key =>
  if name == "Base" then match key with
    | .capacity => some (fun context => ⟨context + 10, by omega⟩)
    | .priority => some (fun _ => false)
    | .label => some (fun _ => "base")
    | .legacy => none
  else none

def plugin (name : String) : Provider Nat Capability Value := fun key =>
  if name == "Plugin" then match key with
    | .priority => some (fun _ => true)
    | _ => none
  else none

abbrev positive : List Capability := [.capacity]
def Joint (context : Nat) (data : Results Value context (positive ++ workload.analyze.required)) : Prop :=
  data.1.val ≤ context + 10
def Valid (context : Nat) (plan : Plan context) : Prop := plan.val.sum ≤ context + 10

theorem admitJoint (provider : Provider Nat Capability Value) (factories)
    (_selected : Selected provider (positive ++ workload.analyze.required) factories) :
    ∀ context, Joint context (build factories context) := fun _ => ((build factories _).1).property

theorem admitResult (provider : Provider Nat Capability Value) :
    ∀ context, Computation.OutcomeValid Valid context (workload.evaluate provider context) := by
  intro context
  cases workload.evaluate provider context with
  | error error => trivial
  | ok plan => exact plan.property

-- Publication still asks for both admissions on fresh paths. Reused paths
-- retain their existing proofs and their exact hot result/error slot.
def publish {registry : IndexedRegistry Nat Capability Value}
    {newProviders : String → Provider Nat Capability Value} {edits : List (RegistryEdit Nat Capability Value)}
    {graph : C4.Graph} {root : String} {target : PreparedGraphMigration registry graph root newProviders edits}
    (revision : AnalyzedConstraintRevision target workload positive [] Joint Valid) :=
  revision.certify (by
    cases revision.capabilities.positive with
    | reused _ _ _ => trivial
    | fresh prepared available => exact admitJoint _)
    (by cases revision.computed with
        | reused _ => trivial
        | fresh => exact admitResult _)

structure Change where
  name : String
  graph : C4.Graph
  newcomers : String → Provider Nat Capability Value
  edits : List (RegistryEdit Nat Capability Value)

def changes : List Change := [
  ⟨"unrelated label", oldGraph, plugin, [("Base", [⟨.label, some (fun _ => "new")⟩])]⟩,
  ⟨"priority plugin", extendedGraph, plugin, []⟩,
  ⟨"lower limit", oldGraph, plugin, [("Base", [⟨.capacity, some (fun c => ⟨c+1, by omega⟩)⟩])]⟩,
  ⟨"legacy conflict", extendedGraph, plugin, [("Plugin", [⟨.legacy, some (fun _ => (1 : Nat))⟩])]⟩,
  ⟨"conflict and missing", extendedGraph, plugin,
    [("Plugin", [⟨.legacy, some (fun _ => (1 : Nat))⟩]), ("Base", [⟨.capacity, none⟩])]⟩,
  ⟨"add then remove legacy", oldGraph, plugin,
    [("Base", [⟨.legacy, some (fun _ => (1 : Nat))⟩, ⟨.legacy, none⟩])]⟩,
  ⟨"missing limit", oldGraph, plugin, [("Base", [⟨.capacity, none⟩])]⟩,
  ⟨"unknown provider", oldGraph, plugin, [("Unknown", [⟨.label, some (fun _ => "bad")⟩])]⟩,
  ⟨"cyclic graph", cyclicGraph, plugin, []⟩]

def display {context : Nat} : Except (ComputationError Capability) (Plan context) → String
  | .ok plan => s!"amounts={plan.val}, sum={plan.val.sum}"
  | .error error => reprStr error

def scenario (context : Nat) : IO Unit := do
  let .ok order := C4.linearizeVerified oldGraph "Root" | throw (IO.userError "old graph")
  let registry := IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph providers)
  let provider := assemble order registry.dictionary
  let raw := cacheCertified provider (positive ++ workload.analyze.required) Joint (admitJoint provider)
  let .ok absent := checkAbsent provider workload.analyze.forbidden | throw (IO.userError "old absences")
  let capabilities : ConstraintCache provider _ _ Joint := ⟨raw, BuiltContextCache.empty raw, absent⟩
  let cache := AnalyzedConstraintCache.start (code := workload) (positive := positive) (negative := [])
    capabilities (admitResult provider)
  let (original, warm, _) := cache.read context
  let .ok built := warm.capabilities.read context | throw (IO.userError "old capability cache")
  let warm := {warm with capabilities := built.next}
  IO.println s!"context={context}, original: {display original.val}"
  for change in changes do
    match migrateAnalyzedConstraints order.indexAncestors warm change.graph "Root" change.newcomers change.edits with
    | .error error =>
      match error with
      | .provider name =>
        unless change.name == "unknown provider" && name == "Unknown" do
          throw (IO.userError "unexpected provider refusal")
      | .graph (.cycle _) =>
        unless change.name == "cyclic graph" do throw (IO.userError "unexpected cycle refusal")
      | _ => throw (IO.userError "unexpected graph refusal")
      IO.println s!"{change.name}: preparation refused {repr error}"
    | .ok ⟨_target, .error (.introduced conflict)⟩ =>
      unless (change.name == "legacy conflict" || change.name == "conflict and missing") &&
          conflict.key == .legacy do throw (IO.userError "wrong negative conflict/priority")
      IO.println s!"{change.name}: introduced forbidden {repr conflict.key}, no publication"
    | .ok ⟨_target, .error (.missing key _)⟩ =>
      unless change.name == "missing limit" && key == .capacity do throw (IO.userError "wrong missing key")
      IO.println s!"{change.name}: missing {repr key}, no publication"
    | .ok ⟨target, .ok revision⟩ =>
      let published := publish revision
      let (outcome, next, hit) := published.read context
      let (_, _, repeated) := next.read context
      unless repeated do throw (IO.userError "second read must hit")
      let expectedReuse := change.name == "unrelated label" || change.name == "add then remove legacy"
      unless revision.computed.isReused == expectedReuse && hit == expectedReuse do
        throw (IO.userError "wrong computed revision/hot-slot policy")
      match outcome.val with
      | .ok plan =>
        let expected := if expectedReuse then [context+2, context+3] else [context+1, context+2]
        unless plan.val == expected && change.name != "lower limit" do
          throw (IO.userError "workload differs from independent amounts")
      | .error (.source message) =>
        let expected := if change.name == "lower limit" then "job outside capacity"
          else "combined workload outside capacity"
        unless message == expected && (change.name == "lower limit" || expectedReuse && context == 7) do
          throw (IO.userError "wrong workload source error")
      | _ => throw (IO.userError "published workload exposed a capability error")
      unless display outcome.val == display (workload.evaluate (assemble target.index.order target.registry.dictionary) context) do
        throw (IO.userError "published cache disagrees with actual target")
      -- A second migration uses the newly published registry and cache.
      let .ok nextTarget := prepareGraphMigration target.registry change.graph "Root" plugin [] |
        throw (IO.userError "continuation graph")
      let .ok continuation := reviseAnalyzedConstraints target.index next nextTarget |
        throw (IO.userError "continuation policy")
      let continued := publish continuation
      let (same, _, stillHot) := continued.read context
      unless continuation.computed.isReused && stillHot && display same.val == display outcome.val do
        throw (IO.userError "second migration lost retained success/error")
      let (_, moved, differentContext) := continued.read (context+1)
      let (_, _, oldContext) := moved.read context
      unless !differentContext && !oldContext do throw (IO.userError "context-slot replacement failed")
      IO.println s!"{change.name}: reused={revision.computed.isReused}, hot={hit}, {display outcome.val}"

#eval scenario 2
#eval scenario 7
end LeanPoo.Examples.IncrementalWorkflow
