import LeanPoo.Functional.GraphConstraints

namespace LeanPoo.Tests.FunctionalGraphConstraints
open Functional Functional.Requirements
universe u v w

example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key]
    [LawfulBEq Key] [DecidableEq Key] {Value : Context → Key → Type w}
    {registry : IndexedRegistry Context Key Value} (positive negative : List Key)
    (Claim : ∀ c, Results Value c positive → Prop)
    (old : C4.AncestryIndex oldGraph oldRoot)
    (cache : ConstraintCache (assemble old.order registry.dictionary) positive negative Claim)
    (newProviders : String → Provider Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (target : PreparedGraphMigration registry graph root newProviders edits) :
    (∃ revision, reviseGraphConstraints old cache (KeyIndex.ofKeys positive) target = .ok revision) ↔
      Absent (assemble target.index.order target.registry.dictionary) negative ∧
      ∃ factories, prepare (assemble target.index.order target.registry.dictionary) positive = .ok factories :=
  reviseGraphConstraints_ok_iff old cache (KeyIndex.ofKeys positive) target

example {Context : Type u} [DecidableEq Context] {Key : Type v}
    {Value : Context → Key → Type w} {provider : Provider Context Key Value}
    {positive negative : List Key} {Claim : ∀ c, Results Value c positive → Prop}
    (cache : ConstraintCache provider positive negative Claim) (c : Context)
    (read : ConstraintRead cache c) (ready : Certified positive Claim)
    (selected : cache.positive.outcome = .ok ready) :
    read.data = build ready.factories c ∧ Claim c read.data := ⟨read.aligned ready selected, read.correct⟩

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    (oldProvider _nextProvider : Provider Context Key Value) (positive negative : List Key)
    (Claim : ∀ c, Results Value c positive → Prop)
    (_cache : ConstraintCache oldProvider positive negative Claim) : True := by
  fail_if_success have _stale : ConstraintCache _nextProvider positive negative Claim := _cache
  trivial

private inductive Key where
  | quantity | flag | proof | forbidden | unforced
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq
private instance : Hashable Key where
  hash _ := 0
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .proof => PLift (c ≤ c + 1)
  | .forbidden | .unforced => Nat
private partial def neverFinish (c : Nat) : Nat := neverFinish c
private def source (n : Nat) : (key : Key) → Factory Nat (fun c => Value c key)
  | .quantity => fun c => ⟨c+n, by omega⟩
  | .flag => fun c => c % 2 == 0
  | .proof => Factory.fromProof (fun _ => by omega)
  | .forbidden => fun c => c+n
  | .unforced => neverFinish
private def provided (mask : Nat) (name : String) (key : Key) : Bool :=
  if name == "Outside" then key == .forbidden || key == .unforced
  else if name == "A" || name == "B" then match key with
    | .quantity => mask % 2 == 1
    | .flag => mask / 2 % 2 == 1
    | .proof => mask / 4 % 2 == 1
    | _ => false
  else false
private def providers (mask : Nat) (name : String) : Provider Nat Key Value := fun key =>
  if provided mask name key then some (source (if name == "A" then 1 else 2) key) else none
private def newcomer (name : String) : Provider Nat Key Value := fun key =>
  if name == "New" && key == .quantity then some (source 8 key) else none
private abbrev Step := String × Key × Bool × Nat
private def changes (steps : List Step) : List (RegistryEdit Nat Key Value) :=
  steps.map fun (name, key, add, n) => (name, [⟨key, if add then some (source n key) else none⟩])
private def values : {keys : List Key} → Results Value c keys → List Nat
  | [], _ => []
  | .quantity :: _, (q, tail) => q.val :: values tail
  | .flag :: _, (b, tail) => (if (show Bool from b) then 1 else 0) :: values tail
  | .proof :: _, (_, tail) => 1 :: values tail
  | .forbidden :: _, (n, tail) => n :: values tail
  | .unforced :: _, (n, tail) => n :: values tail
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
private def isPresent (mask : Nat) (declared : List String) (steps : List Step)
    (name : String) (key : Key) : Bool :=
  declared.contains name && steps.foldl (fun prior (changed, k, add, _) =>
    if name == changed && key == k then add else prior)
    (if (oldGraph.nodes.map C4.Node.name).contains name then provided mask name key
     else name == "New" && key == .quantity)
private def scalar (mask : Nat) (declared order : List String) (steps : List Step)
    (keys : List Key) (c : Nat) : Except Key (List Nat) := do
  let mut output := []
  for key in keys do
    let some name := order.find? (fun name => isPresent mask declared steps name key) | throw key
    let n := steps.foldl (fun n (changed, k, add, value) =>
      if name == changed && key == k && add then value else n)
      (if name == "A" then 1 else if name == "New" then 8 else 2)
    output := output ++ [match key with
      | .quantity | .forbidden | .unforced => c + n
      | .flag => if c % 2 == 0 then 1 else 0
      | .proof => 1]
  return output
private def jointKeys : List Key := [.quantity, .quantity, .flag, .proof]
private def Joint (c : Nat) (data : Results Value c jointKeys) : Prop :=
  data.1 = data.2.1 ∧ c ≤ data.1.val
private theorem joint_admit (provider : Provider Nat Key Value)
    (f : Factories Nat Value jointKeys) (selected : Selected provider jointKeys f) :
    ∀ c, Joint c (build f c) := by
  rcases f with ⟨q, other, flag, proof, empty⟩
  have same : q = other := Option.some.inj (selected.1.symm.trans selected.2.1)
  subst other
  intro c
  exact ⟨rfl, (q c).property⟩

#eval do
  IO.println "FUNCTIONAL-GRAPH-CONSTRAINTS-START"
  let .ok oldOrder := C4.linearizeVerified oldGraph "Root" | throw (IO.userError "old graph")
  let old := oldOrder.indexAncestors
  let positives : List (List Key) := [[], [.quantity], [.flag], [.proof], [.quantity, .flag, .proof],
    [.quantity, .quantity], [.flag, .quantity, .flag]]
  let negatives : List (List Key) := [[], [.forbidden], [.unforced], [.forbidden, .unforced, .forbidden], [.flag]]
  let plans : List (List Step) := [[], [("B", .quantity, true, 17)], [("A", .quantity, false, 0)],
    [("B", .forbidden, true, 5)], [("B", .forbidden, true, 5), ("B", .forbidden, false, 0)],
    [("New", .quantity, true, 12)], [("Missing", .quantity, true, 12), ("Later", .flag, false, 0)]]
  let mut cases := 0
  let mut reuse := 0
  let mut fresh := 0
  let mut refused := 0
  for mask in List.range 8 do
    let registry : IndexedRegistry Nat Key Value :=
      IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (providers mask))
    for positive in positives do
      let claim := fun _ (_ : Results Value _ positive) => True
      let cached := cacheCertified (assemble oldOrder registry.dictionary) positive claim (fun _ _ _ => True.intro)
      for negative in negatives do
        match checkAbsent (assemble oldOrder registry.dictionary) negative with
        | .error _ => pure ()
        | .ok absence =>
          let initial : ConstraintCache _ positive negative claim := ⟨cached, BuiltContextCache.empty cached, absence⟩
          let warmed := match initial.read 7 with | .error _ => initial | .ok read => read.next
          for graph in targets do
            let root := if (graph.nodes.map C4.Node.name).contains "Wrapper" then "Wrapper" else "Root"
            let declared := graph.nodes.map C4.Node.name
            for steps in plans do
              let outcome := migrateGraphConstraints old warmed (KeyIndex.ofKeys positive) graph root newcomer (changes steps)
              let missing := steps.find? (fun (step : Step) => !declared.contains step.1)
              match outcome, missing with
              | .error (.provider name), some first =>
                unless name == first.1 do throw (IO.userError "first unknown name")
              | .ok ⟨target, revision⟩, none =>
                let order := target.index.order.output
                let conflict := negative.find? (fun key => order.any fun name => isPresent mask declared steps name key)
                match revision, conflict, scalar mask declared order steps positive 7 with
                | .error (.introduced actual), some key, _ =>
                  unless actual.key == key do throw (IO.userError "first negative conflict")
                  let _negativeProof := actual.prior
                  refused := refused + 1
                | .error (.missing key _), none, .error expected =>
                  unless key == expected do throw (IO.userError "first positive error")
                  refused := refused + 1
                | .ok accepted, none, .ok expected =>
                  let kept := target.canReuse oldOrder (KeyIndex.ofKeys positive)
                  let admission : accepted.positive.Admission := by
                    cases accepted.positive with
                    | reused _ _ _ => trivial
                    | fresh _ _ => exact fun _ _ _ => True.intro
                  let next := accepted.certify admission
                  let .ok read := next.read 7 | throw (IO.userError "accepted cache lost positives")
                  unless values read.data == expected && read.reused == kept do
                    throw (IO.userError "new graph reused stale context data or discarded hot data")
                  let .ok hot := read.next.read 7 | throw (IO.userError "hot read failed")
                  let .ok changed := hot.next.read 0 | throw (IO.userError "context change failed")
                  unless hot.reused && !changed.reused do throw (IO.userError "context cache lifetime")
                  let .ok expectedZero := scalar mask declared order steps positive 0 |
                    throw (IO.userError "reference availability changed by context")
                  unless values changed.data == expectedZero do throw (IO.userError "stale context cast")
                  -- A second migration uses the actually published registry and index.
                  let .ok chain := prepareGraphMigration target.registry graph root newcomer [] |
                    throw (IO.userError "second compile")
                  let .ok continued := reviseGraphConstraints target.index read.next (KeyIndex.ofKeys positive) chain |
                    throw (IO.userError "second capability check")
                  match continued.positive with
                  | .fresh _ _ => throw (IO.userError "unchanged second migration re-prepared")
                  | .reused _ _ _ => pure ()
                  if kept then reuse := reuse + 1 else fresh := fresh + 1
                | _, _, _ => throw (IO.userError "joint capability guard differs from independent model")
                cases := cases + 1
              | _, _ => throw (IO.userError "graph/provider priority")
  -- A genuine joint contract survives graph changes without accepting a stale family.
  let registry : IndexedRegistry Nat Key Value :=
    IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph oldGraph (providers 7))
  let provider := assemble oldOrder registry.dictionary
  let cached := cacheCertified provider jointKeys Joint (joint_admit provider)
  let .ok absent := checkAbsent provider [.forbidden] | throw (IO.userError "joint absence")
  let initial : ConstraintCache provider jointKeys [.forbidden] Joint := ⟨cached, BuiltContextCache.empty cached, absent⟩
  let .ok warm := initial.read 7 | throw (IO.userError "joint warm")
  for graph in targets.take 4 do
    let root := if (graph.nodes.map C4.Node.name).contains "Wrapper" then "Wrapper" else "Root"
    let .ok ⟨target, .ok accepted⟩ := migrateGraphConstraints old warm.next (KeyIndex.ofKeys jointKeys)
        graph root newcomer [] | throw (IO.userError "joint migration")
    let admission : accepted.positive.Admission := by
      cases accepted.positive with
      | reused _ _ _ => trivial
      | fresh _ _ => exact joint_admit (assemble target.index.order target.registry.dictionary)
    let .ok data := (accepted.certify admission).read 7 | throw (IO.userError "joint read")
    let _actualJoint := data.correct
    unless data.data.1.val == data.data.2.1.val do throw (IO.userError "joint duplicate agreement")
  unless cases == 6300 && reuse == 1087 && fresh == 1537 && refused == 3676 do
    throw (IO.userError "graph constraint coverage changed")
  -- Presence checks above diagnose a nonterminating factory without forcing it.
  IO.println s!"FUNCTIONAL-GRAPH-CONSTRAINTS-OK cases={cases} reused={reuse} fresh={fresh} refused={refused}"

#print axioms LeanPoo.Functional.Requirements.reviseGraphConstraints_ok_iff
#print axioms LeanPoo.Functional.Requirements.PositiveGraphRevision.certify_forget
#print axioms LeanPoo.Functional.Requirements.PositiveGraphRevision.certify_reused
#print axioms LeanPoo.Functional.Requirements.GraphConstraintRevision.certify_available
end LeanPoo.Tests.FunctionalGraphConstraints
