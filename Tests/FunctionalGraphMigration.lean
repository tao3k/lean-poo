import LeanPoo.Functional.GraphMigration

namespace LeanPoo.Tests.FunctionalGraphMigration
open Functional Functional.Requirements
universe u v w

example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key]
    [LawfulBEq Key] [DecidableEq Key] {Value : Context → Key → Type w}
    (registry : IndexedRegistry Context Key Value) (oldOrder : C4.VerifiedOrder oldGraph oldRoot)
    (keys : List Key) (newProviders : String → Provider Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) (scope : KeyIndex keys) (target : PreparedGraphMigration registry graph root newProviders edits)
    (retained : target.canReuse oldOrder scope = true) :
    prepare (assemble target.index.order target.registry.dictionary) keys =
      prepare (assemble oldOrder registry.dictionary) keys := target.reuse_preparation oldOrder scope retained

private inductive Key where
  | quantity | flag
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq
private instance : Hashable Key where
  hash _ := 0
private abbrev Value := fun (_ : Nat) (_ : Key) => Nat
private def oldGraph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["A", "B"]]},
  {name := "A"}, {name := "B"}, {name := "Outside"}]}
private def present (mask : Nat) (name : String) (key : Key) : Bool :=
  (name == "A" || name == "B") && mask / (if key == .quantity then 1 else 2) % 2 == 1
private def initial (mask : Nat) (name : String) : Provider Nat Key Value := fun key =>
  if present mask name key then some (fun c => c + (if name == "A" then 1 else 2)) else none
private def newcomers (name : String) : Provider Nat Key Value := fun key =>
  if name == "New" && key == .quantity then some (fun c => c + 8)
  else if name == "A" then some (fun _ => 999) else none
private abbrev Step := String × Key × Option Nat
private def changes (steps : List Step) : List (RegistryEdit Nat Key Value) :=
  steps.map fun (name, key, value) => (name, [⟨key, value.map fun n c => c + n⟩])
private def state (mask : Nat) (declared : List String) (steps : List Step)
    (name : String) (key : Key) (c : Nat) : Option Nat :=
  if !declared.contains name then none else
    steps.foldl (fun prior (source, changed, value) =>
      if source == name && changed == key then value.map (c + ·) else prior)
      (if name == "A" then (if key == .quantity then some (c + 42) else none)
       else if (oldGraph.nodes.map C4.Node.name).contains name then
         if present mask name key then some (c + 2) else none
       else if name == "New" && key == .quantity then some (c + 8) else none)
private def results : {keys : List Key} → Results Value c keys → List Nat
  | [], _ => []
  | _ :: _, (head, tail) => head :: results tail
private def same : Except Key (List Nat) → Except Key (List Nat) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false
private def oracle (mask : Nat) (declared order : List String) (steps : List Step)
    (keys : List Key) (c : Nat) : Except Key (List Nat) := do
  let mut output := []
  for key in keys do
    let some n := order.findSome? (fun name => state mask declared steps name key c) | throw key
    output := output ++ [n]
  return output
private def targets : List (C4.Graph × String) :=
  [({nodes := oldGraph.nodes ++ [{name := "Wrapper", parentOrders := [["Root"]]}]}, "Wrapper"),
   ({nodes := [{name := "Root", parentOrders := [["B", "A"]]}, {name := "A"},
      {name := "B"}, {name := "Outside"}]}, "Root"),
   ({nodes := [{name := "Root", parentOrders := [["B"]]}, {name := "B"}]}, "Root"),
   ({nodes := [{name := "Root", parentOrders := [["New", "B"]]}, {name := "New"},
      {name := "B"}]}, "Root"),
   ({nodes := [{name := "Root"}, {name := "A"}, {name := "B"}]}, "Root"),
   ({nodes := [{name := "Root", parentOrders := [["A", "B"]]}, {name := "A"},
      {name := "B", suffix := true}]}, "Root"),
   (oldGraph, "A"), (oldGraph, "Outside")]

#eval do
  IO.println "FUNCTIONAL-GRAPH-MIGRATION-START"
  let .ok oldOrder := C4.linearizeVerified oldGraph "Root" | throw (IO.userError "old graph")
  let watches : List (List Key) := [[], [.quantity], [.flag], [.quantity, .flag], [.flag, .quantity, .flag]]
  let plans : List (List Step) := [[], [("B", .quantity, some 17)], [("A", .quantity, none)],
    [("A", .quantity, some 12), ("A", .quantity, none)], [("New", .flag, some 5)],
    [("Outside", .quantity, some 9)], [("Missing", .quantity, none), ("LaterMissing", .flag, none)]]
  let mut cases := 0
  let mut retained := 0
  for mask in List.range 4 do
    let base : IndexedRegistry Nat Key Value := IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (initial mask))
    let .ok registry := base.patchTransaction (changes [("A", .quantity, some 42), ("A", .flag, none)]) |
      throw (IO.userError "seed overlay")
    for (graph, root) in targets do
      let declared := graph.nodes.map C4.Node.name
      for steps in plans do
        let result := prepareGraphMigration registry graph root newcomers (changes steps)
        let missing := steps.find? (fun (step : Step) => !declared.contains step.1)
        match result, missing with
        | .error (.provider name), some expected =>
          unless name == expected.1 do throw (IO.userError "first unknown target provider")
        | .ok target, none =>
          let _actualCompilation := target.compiled
          let _actualTransaction := target.applied
          -- Independent scalar state model checks all target declarations, including non-ancestors.
          for name in declared ++ ["Removed", "Missing", "New", "A", "Outside"] do
            for key in [Key.quantity, .flag] do
              unless ((target.registry.dictionary name key).map (fun (f : Nat → Nat) => f 3)) ==
                  state mask declared steps name key 3 do throw (IO.userError "lost overlay/new/removal")
          for keys in watches do
            let scope := KeyIndex.ofKeys keys
            let candidate := target.canReuse oldOrder scope
            let beforeOrigin := fun key => oldOrder.output.find? fun name =>
              (state mask (oldGraph.nodes.map C4.Node.name) [] name key 0).isSome
            let nextOrigin := fun key => target.index.order.output.find? fun name =>
              (state mask declared [] name key 0).isSome
            let expected := keys.all (fun key => beforeOrigin key == nextOrigin key) &&
              !(steps.any fun step => target.index.order.output.contains step.1 && keys.contains step.2.1)
            unless candidate == expected do throw (IO.userError "reuse decision ignored next ancestry")
            for c in [0, 7] do
              let actual := (prepare (assemble target.index.order target.registry.dictionary) keys).map
                (fun f => results (build f c))
              unless same actual (oracle mask declared target.index.order.output steps keys c) do
                throw (IO.userError "target selection differs from independent model")
              if candidate then
                let old := (prepare (assemble oldOrder registry.dictionary) keys).map (fun f => results (build f c))
                unless same actual old do throw (IO.userError "reuse changed selected factories")
            if candidate then retained := retained + 1
            cases := cases + 1
        | _, _ => throw (IO.userError "unexpected graph/provider outcome")
    unless ((registry.dictionary "A" .quantity).map (fun (f : Nat → Nat) => f 3)) == some 45 do
      throw (IO.userError "pure migration altered old registry")
  let empty : IndexedRegistry Nat Key Value := ⟨{}⟩
  let bad : List C4.Graph := [{nodes := [{name := "Root", parentOrders := [["Missing"]]}]},
    {nodes := [{name := "Root", parentOrders := [["Root"]]}]},
    {nodes := [{name := "Root"}, {name := "Root"}]}]
  for graph in bad do
    match prepareGraphMigration empty graph "Root" newcomers (changes [("MissingEdit", .quantity, none)]) with
    | .error (.graph _) => pure ()
    | _ => throw (IO.userError "provider error hid graph compilation failure")
  unless cases == 660 && retained == 304 do throw (IO.userError "graph migration coverage changed")
  IO.println s!"FUNCTIONAL-GRAPH-MIGRATION-OK cases={cases} retained={retained}"

#print axioms LeanPoo.Functional.IndexedRegistry.regraph_retained
#print axioms LeanPoo.Functional.regraph_selection_same
#print axioms LeanPoo.Functional.prepareGraphMigration_ok_iff
#print axioms LeanPoo.Functional.PreparedGraphMigration.reuse_preparation
end LeanPoo.Tests.FunctionalGraphMigration
