import LeanPoo.Functional.AnalyzedMigration

namespace LeanPoo.Tests.FunctionalAnalyzedMigration
open Functional Functional.Requirements
universe u v w

example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key]
    [LawfulBEq Key] [DecidableEq Key] {Value : Context → Key → Type w}
    {Result : Context → Type w} {registry : IndexedRegistry Context Key Value}
    (code : Computation Context Key Value Result) (old : C4.AncestryIndex oldGraph oldRoot)
    (positive negative : List Key) (Joint : ∀ c, Results Value c (positive ++ code.analyze.required) → Prop)
    (Claim : ∀ c, Result c → Prop)
    (cache : AnalyzedConstraintCache code (assemble old.order registry.dictionary) positive negative Joint Claim)
    {newProviders : String → Provider Context Key Value} {edits : List (RegistryEdit Context Key Value)}
    (target : PreparedGraphMigration registry graph root newProviders edits) :
    (∃ revision, reviseAnalyzedConstraints old cache target = .ok revision) ↔
      Absent (assemble target.index.order target.registry.dictionary) (negative ++ code.analyze.forbidden) ∧
      ∃ f, prepare (assemble target.index.order target.registry.dictionary) (positive ++ code.analyze.required) = .ok f :=
  reviseAnalyzedConstraints_ok_iff old cache target

private inductive Key where
  | quantity | flag | proof | ghost | trap
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr
private instance : Hashable Key where hash _ := 0
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .proof => PLift (c ≤ c+1)
  | .ghost | .trap => Nat
private partial def neverFinish (c : Nat) : Nat := neverFinish c
private def source (n : Nat) : (key : Key) → Factory Nat (fun c => Value c key)
  | .quantity => fun c => ⟨c+n, by omega⟩
  | .flag => fun c => (c+n) % 2 == 0
  | .proof => Factory.fromProof (fun _ => by omega)
  | .ghost => fun c => c+n
  | .trap => neverFinish
private def provided (mask : Nat) (name : String) (key : Key) : Bool :=
  if name == "Outside" then key == .ghost || key == .trap
  else if name == "A" || name == "B" then match key with
    | .quantity => mask % 2 == 1
    | .flag => mask / 2 % 2 == 1
    | .proof => mask / 4 % 2 == 1
    | _ => false
  else false
private def providers (mask : Nat) (name : String) : Provider Nat Key Value := fun key =>
  if provided mask name key then some (source (if name == "A" then 1 else 2) key) else none
private def newcomer (name : String) : Provider Nat Key Value := fun key =>
  if name == "New" && (key == .quantity || key == .flag) then some (source 8 key) else none
private abbrev Step := String × Key × Bool × Nat
private def changes (steps : List Step) : List (RegistryEdit Nat Key Value) :=
  steps.map fun (name, key, add, n) => (name, [⟨key, if add then some (source n key) else none⟩])
private def oldGraph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["A", "B"]]},
  {name := "A"}, {name := "B"}, {name := "Outside"}]}
private def targets : List C4.Graph :=
  [{nodes := oldGraph.nodes ++ [{name := "Wrapper", parentOrders := [["Root"]]}]},
   {nodes := [{name := "Root", parentOrders := [["B", "A"]]}, {name := "A"}, {name := "B"}]},
   {nodes := [{name := "Root", parentOrders := [["B"]]}, {name := "B"}]},
   {nodes := [{name := "Root", parentOrders := [["New", "B"]]}, {name := "New"}, {name := "B"}]},
   {nodes := [{name := "Root"}]},
   {nodes := [{name := "Root", parentOrders := [["Outside", "A", "B"]]},
      {name := "A"}, {name := "B"}, {name := "Outside"}]}]
private def present (mask : Nat) (declared : List String) (steps : List Step)
    (name : String) (key : Key) : Bool :=
  declared.contains name && steps.foldl (fun prior (changed, k, add, _) =>
    if name == changed && key == k then add else prior)
    (if (oldGraph.nodes.map C4.Node.name).contains name then provided mask name key
     else name == "New" && (key == .quantity || key == .flag))
private def origin (mask : Nat) (declared order : List String) (steps : List Step) (key : Key) : Option String :=
  order.find? (fun name => present mask declared steps name key)
private def number (name : String) (steps : List Step) (key : Key) : Nat :=
  steps.foldl (fun prior (changed, k, add, n) => if name == changed && key == k && add then n else prior)
    (if name == "A" then 1 else if name == "New" then 8 else 2)
private def optional (mask : Nat) (declared order : List String) (steps : List Step)
    (key : Key) (c : Nat) : Option Nat := do
  let name ← origin mask declared order steps key
  let n := number name steps key
  return match key with
    | .quantity | .ghost => c+n
    | .flag => if (c+n) % 2 == 0 then 1 else 0
    | .proof => 1
    | .trap => 0 -- No test evaluates a trap; only presence checks observe it.

private def body (id : Nat) : Computation Nat Key Value (fun _ => Nat) :=
  match id with
  | 0 => .both (.map (.need .quantity (fun _ q => q.val)) (fun _ n => n))
      (.read .flag (fun _ b => if (show Bool from b.getD false) then 1 else 0)) (fun _ q b => q+b)
  | 1 => .inspect .flag (fun _ b => if b then 1 else 0)
  | 2 => .both (.need .quantity (fun _ q => q.val)) (.deny .ghost (fun _ => 1)) (fun _ q n => q+n)
  | 3 => .both (.need .quantity (fun _ q => q.val)) (.need .proof (fun _ _ => 1)) (fun _ q n => q+n)
  | 4 => .opaque (fun provider c => match provider .quantity with
      | none => .error (.missing .quantity) | some factory => .ok (factory c).val)
  | 5 => .choose (.need .flag (fun _ b => b)) (fun _ b => b)
      (.need .quantity (fun _ q => q.val)) (.read .ghost (fun _ n => (show Option Nat from n).getD 0))
  | _ => .failure "retained-source-error"
-- This independent table supplies the scalar reuse/contract oracle.
private def dataKeys (id : Nat) : List Key := match id with
  | 0 => [.quantity, .flag] | 2 => [.quantity] | 3 => [.quantity, .proof]
  | 5 => [.flag, .quantity, .ghost] | _ => []
private def presenceKeys (id : Nat) : List Key := match id with
  | 1 => [.flag] | 2 => [.ghost] | _ => []
private def required (id : Nat) : List Key := match id with
  | 0 | 2 => [.quantity] | 3 => [.quantity, .proof] | 5 => [.flag, .quantity] | _ => []
private def forbidden (id : Nat) : List Key := if id == 2 then [.ghost] else []
private def reference (id mask : Nat) (declared order : List String) (steps : List Step)
    (c : Nat) : Except (ComputationError Key) Nat := do
  let q : Except (ComputationError Key) Nat :=
    match optional mask declared order steps .quantity c with
    | none => .error (.missing .quantity) | some n => .ok n
  match id with
  | 0 => return (← q) + (optional mask declared order steps .flag c).getD 0
  | 1 => return if (origin mask declared order steps .flag).isSome then 1 else 0
  | 2 =>
    let n ← q
    if (origin mask declared order steps .ghost).isSome then throw (.introduced .ghost) else return n+1
  | 3 =>
    let n ← q
    if (origin mask declared order steps .proof).isSome then return n+1 else throw (.missing .proof)
  | 4 => q
  | 5 =>
    let some flag := optional mask declared order steps .flag c | throw (.missing .flag)
    if flag == 1 then q else return (optional mask declared order steps .ghost c).getD 0
  | _ => throw (.source "retained-source-error")
private def same : Except (ComputationError Key) Nat → Except (ComputationError Key) Nat → Bool
  | .ok a, .ok b => a == b | .error a, .error b => a == b | _, _ => false
private theorem result_admit (code : Computation Nat Key Value (fun _ => Nat))
    (provider : Provider Nat Key Value) (c : Nat) :
    Computation.OutcomeValid (fun _ (_ : Nat) => True) c (code.evaluate provider c) := by
  cases code.evaluate provider c <;> trivial

#eval do
  IO.println "FUNCTIONAL-ANALYZED-MIGRATION-START"
  let .ok oldOrder := C4.linearizeVerified oldGraph "Root" | throw (IO.userError "old graph")
  let old := oldOrder.indexAncestors
  let oldDeclared := oldGraph.nodes.map C4.Node.name
  let plans : List (List Step) := [[], [("B", .flag, true, 19)], [("A", .flag, true, 20)],
    [("A", .quantity, false, 0)], [("B", .proof, false, 0)], [("B", .ghost, true, 4)],
    [("B", .ghost, true, 4), ("B", .ghost, false, 0)],
    [("Missing", .flag, true, 4), ("Later", .quantity, false, 0)]]
  let mut cases := 0
  let mut reused := 0
  let mut fresh := 0
  let mut refused := 0
  let mut hiddenFresh := 0
  let mut presenceReuse := 0
  let mut unknownFresh := 0
  for mask in List.range 8 do
    let registry : IndexedRegistry Nat Key Value :=
      IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (providers mask))
    let provider := assemble oldOrder registry.dictionary
    for id in List.range 7 do
      let code := body id
      let positive : List Key := [.quantity]
      let negative : List Key := []
      let joint := fun _ (_ : Results Value _ (positive ++ code.analyze.required)) => True
      let raw := cacheCertified provider (positive ++ code.analyze.required) joint (fun _ _ _ => True.intro)
      let .ok absence := checkAbsent provider (negative ++ code.analyze.forbidden) |
        throw (IO.userError "old inferred absence")
      let capabilities : ConstraintCache provider _ _ joint := ⟨raw, BuiltContextCache.empty raw, absence⟩
      let initial := AnalyzedConstraintCache.start (code := code) (positive := positive) (negative := negative)
        capabilities (result_admit code provider)
      let (_, warmed, _) := initial.read 7
      let warmed := match warmed.capabilities.read 7 with
        | .error _ => warmed | .ok read => {warmed with capabilities := read.next}
      for graph in targets do
        let root := if (graph.nodes.map C4.Node.name).contains "Wrapper" then "Wrapper" else "Root"
        let declared := graph.nodes.map C4.Node.name
        for steps in plans do
          let unknown := steps.find? (fun (step : Step) => !declared.contains step.1)
          match migrateAnalyzedConstraints old warmed graph root newcomer (changes steps), unknown with
          | .error (.provider name), some first =>
            unless name == first.1 do throw (IO.userError "first unknown provider")
          | .ok ⟨target, outcome⟩, none =>
            let order := target.index.order.output
            let conflict := (forbidden id).find? (fun key => (origin mask declared order steps key).isSome)
            let missing := (positive ++ required id).find? (fun key => !(origin mask declared order steps key).isSome)
            match outcome, conflict, missing with
            | .error (.introduced actual), some expected, _ =>
              unless actual.key == expected do throw (IO.userError "inferred negative priority")
              refused := refused+1
            | .error (.missing actual _), none, some expected =>
              unless actual == expected do throw (IO.userError "inferred positive priority")
              refused := refused+1
            | .ok accepted, none, none =>
              let oldOrigin := origin mask oldDeclared oldOrder.output []
              let beforeEdit := origin mask declared order []
              let expected := id != 4 && (dataKeys id).all (fun key =>
                  beforeEdit key == oldOrigin key && !(steps.any fun (name, k, _, _) => order.contains name && k == key)) &&
                (presenceKeys id).all (fun key => (origin mask declared order steps key).isSome == (oldOrigin key).isSome)
              unless accepted.computed.isReused == expected &&
                  target.canReuseComputation oldOrder code warmed.dependencyScope == expected do
                throw (IO.userError "computed reuse differs from independent origin/presence model")
              let jointAdmission : accepted.capabilities.positive.Admission := by
                cases accepted.capabilities.positive with
                | reused _ _ _ => trivial | fresh _ _ => exact fun _ _ _ => True.intro
              let resultAdmission : accepted.computed.Admission := by
                cases accepted.computed with
                | reused _ => trivial | fresh => exact result_admit code _
              let next := accepted.certify jointAdmission resultAdmission
              let (data, hotCache, hit) := next.read 7
              unless hit == expected && same data.val (reference id mask declared order steps 7) do
                throw (IO.userError "inferred dependency migration returned stale value/error or lost hot slot")
              let _contract := data.property.2
              let (hot, again, hotHit) := hotCache.read 7
              let (changed, _, changedHit) := again.read 0
              unless hotHit && !changedHit && same hot.val data.val &&
                  same changed.val (reference id mask declared order steps 0) do
                throw (IO.userError "computed context lifetime")
              let .ok chain := prepareGraphMigration target.registry graph root newcomer [] |
                throw (IO.userError "second graph")
              let .ok continued := reviseAnalyzedConstraints target.index hotCache chain |
                throw (IO.userError "second contract")
              unless continued.computed.isReused == (id != 4) do throw (IO.userError "second inferred lifetime")
              if expected then reused := reused+1 else fresh := fresh+1
              if id == 0 && target.canReuse oldOrder (KeyIndex.ofKeys positive) && !expected then
                hiddenFresh := hiddenFresh+1
              if id == 1 && steps.any (fun (_, key, _, _) => key == Key.flag) && expected then
                presenceReuse := presenceReuse+1
              if id == 4 then
                unless !hit do throw (IO.userError "opaque callback retained a slot")
                unknownFresh := unknownFresh+1
            | _, _, _ => throw (IO.userError "expanded capability policy differs from scalar model")
            -- The old snapshot retains its hot result even after a refused candidate.
            let (prior, _, priorHit) := warmed.read 7
            unless priorHit && same prior.val (reference id mask oldDeclared oldOrder.output [] 7) do
              throw (IO.userError "migration altered old computed snapshot")
            cases := cases+1
          | _, _ => throw (IO.userError "provider transaction priority")
  -- Presence-only replacement can observe an arbitrarily divergent factory safely.
  let registry : IndexedRegistry Nat Key Value :=
    IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (providers 7))
  let provider := assemble oldOrder registry.dictionary
  let code : Computation Nat Key Value (fun _ => Nat) := .inspect .trap (fun _ b => if b then 1 else 0)
  let raw := cacheCertified provider [] (fun _ _ => True) (fun _ _ _ => True.intro)
  let .ok absence := checkAbsent provider [] | throw (IO.userError "empty absence")
  let capabilities : ConstraintCache provider [] [] (fun _ _ => True) := ⟨raw, BuiltContextCache.empty raw, absence⟩
  let cache := AnalyzedConstraintCache.start (code := code) (positive := []) (negative := []) capabilities (result_admit code provider)
  let (_, warm, _) := cache.read 7
  let .ok target := prepareGraphMigration registry oldGraph "Root" newcomer (changes [("A", .trap, true, 0)]) |
    throw (IO.userError "trap patch")
  let .ok accepted := reviseAnalyzedConstraints old warm target | throw (IO.userError "trap presence")
  unless !accepted.computed.isReused do throw (IO.userError "presence change retained cache")
  let admission : accepted.capabilities.positive.Admission := by
    cases accepted.capabilities.positive with
    | reused _ _ _ => trivial | fresh _ _ => exact fun _ _ _ => True.intro
  let resultAdmission : accepted.computed.Admission := by
    cases accepted.computed with
    | reused _ => trivial | fresh => exact result_admit code _
  let (observed, _, hit) := (accepted.certify admission resultAdmission).read 7
  unless !hit && same observed.val (.ok 1) do throw (IO.userError "presence forced trap")
  -- An inferred absence refuses a divergent factory without executing the body.
  let denied : Computation Nat Key Value (fun _ => Nat) := .deny .trap (fun _ => 1)
  let .ok oldAbsent := checkAbsent provider denied.analyze.forbidden |
    throw (IO.userError "old inferred trap absence")
  let constraints : ConstraintCache provider [] denied.analyze.forbidden (fun _ _ => True) :=
    ⟨raw, BuiltContextCache.empty raw, oldAbsent⟩
  let deniedCache := AnalyzedConstraintCache.start (code := denied) (positive := []) (negative := [])
    constraints (result_admit denied provider)
  let .error (.introduced conflict) := reviseAnalyzedConstraints old deniedCache target |
    throw (IO.userError "inferred divergent absence accepted")
  unless conflict.key == Key.trap do throw (IO.userError "inferred absence key")
  -- Both branches contribute static contracts, even when the guard is constant.
  let branches : Computation Nat Key Value (fun _ => Nat) :=
    .choose (.pure (fun _ => true)) (fun _ b => b)
      (.need .quantity (fun _ q => q.val)) (.deny .quantity (fun _ => 0))
  let emptyRegistry : IndexedRegistry Nat Key Value :=
    IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (providers 0))
  let emptyProvider := assemble oldOrder emptyRegistry.dictionary
  let positive := branches.analyze.required
  let raw := cacheCertified emptyProvider positive (fun _ _ => True) (fun _ _ _ => True.intro)
  let .ok absent := checkAbsent emptyProvider branches.analyze.forbidden |
    throw (IO.userError "old conservative contract")
  let constraints : ConstraintCache emptyProvider positive branches.analyze.forbidden (fun _ _ => True) :=
    ⟨raw, BuiltContextCache.empty raw, absent⟩
  let branchCache := AnalyzedConstraintCache.start (code := branches) (positive := []) (negative := [])
    constraints (result_admit branches emptyProvider)
  let .ok candidate := prepareGraphMigration emptyRegistry oldGraph "Root" newcomer
      (changes [("A", .quantity, true, 4)]) | throw (IO.userError "branch transaction")
  let .error (.introduced overlap) := reviseAnalyzedConstraints old branchCache candidate |
    throw (IO.userError "mutually exclusive static contracts were silently weakened")
  unless overlap.key == Key.quantity do throw (IO.userError "conservative overlap key")
  unless cases == 1792 && reused == 330 && fresh == 514 && refused == 948 &&
      hiddenFresh == 16 && presenceReuse == 18 && unknownFresh == 144 do
    throw (IO.userError "inferred dependency coverage changed")
  IO.println s!"FUNCTIONAL-ANALYZED-MIGRATION-OK cases={cases} reused={reused} fresh={fresh} refused={refused} hidden-fresh={hiddenFresh} presence-reuse={presenceReuse} unknown-fresh={unknownFresh}"

#print axioms LeanPoo.Functional.PreparedGraphMigration.reuse_computation
#print axioms LeanPoo.Functional.reviseAnalyzedConstraints_reuse
#print axioms LeanPoo.Functional.reviseAnalyzedConstraints_ok_iff
#print axioms LeanPoo.Functional.AnalyzedConstraintRevision.evaluate_safe
#print axioms LeanPoo.Functional.Computation.Cache.rebind_read_reused
end LeanPoo.Tests.FunctionalAnalyzedMigration
