import LeanPoo.Functional.IndexedRegistry
namespace LeanPoo.Tests.FunctionalIndexedRegistry
open C4 Functional
universe u v w x
example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key] [LawfulBEq Key]
    [DecidableEq Key] {Value : Context → Key → Type w} {Result : Type x}
    (index : AncestryIndex graph root) (registry updated : IndexedRegistry Context Key Value)
    (name : String) (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchBatch name edits = .ok updated)
    (unaffected : Requirements.batchMayAffect index keys name edits = false)
    (consume : Requirements.Factories Context Value keys → Result) (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble index.order registry.dictionary) keys).map consume)) :
    Claim ((Requirements.prepare (assemble index.order updated.dictionary) keys).map consume) := by
  rw [Requirements.prepare_indexedRegistry_of_unaffected index registry name edits keys applied unaffected]
  exact known
private inductive Capability where
  | quantity | flag | bound
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq
private instance : Hashable Capability := ⟨fun _ => 0⟩
private def Value (c : Nat) : Capability → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .bound => PLift (c ≤ c + 2)
private def available (mask : Nat) (name : String) : Capability → Bool
  | .quantity => name == "Outside" || (mask % 2 == 1 && (name == "A" || name == "B"))
  | .flag => mask / 2 % 2 == 1 && (name == "Left" || name == "B")
  | .bound => mask / 4 % 2 == 1 && name == "A"
private def providers (mask : Nat) (name : String) : Provider Nat Capability Value
  | .quantity => if available mask name .quantity then
      some (fun c => ⟨c + (if name == "A" then 1 else if name == "B" then 2 else 3), by omega⟩) else none
  | .flag => if available mask name .flag then some (fun c => name == "Left" || c % 2 == 0) else none
  | .bound => if available mask name .bound then some (Factory.fromProof (fun _ => by omega)) else none
private def replacement (present : Bool) (value : Nat) : (key : Capability) →
    Option (Factory Nat (fun c => Value c key))
  | .quantity => if present then some (fun c => ⟨c + value, by omega⟩) else none
  | .flag => if present then some (fun _ => value % 2 == 1) else none
  | .bound => if present then some (Factory.fromProof (fun _ => by omega)) else none
private abbrev Step := Capability × Bool × Nat
private def edits (recipe : List Step) : List (CapabilityEdit Nat Capability Value) :=
  recipe.map (fun step => ⟨step.1, replacement step.2.1 step.2.2 step.1⟩)
private def values : {keys : List Capability} → Requirements.Results Value c keys → List Nat
  | [], _ => []
  | .quantity :: _, (head, tail) => head.val :: values tail
  | .flag :: _, (head, tail) => (if (show Bool from head) then 1 else 0) :: values tail
  | .bound :: _, (_, tail) => 1 :: values tail
private def observe (provider : Provider Nat Capability Value) (keys : List Capability) (c : Nat) :
    Except Capability (List Nat) := (Requirements.prepare provider keys).map (fun ready => values (Requirements.build ready c))
private def same : Except Capability (List Nat) → Except Capability (List Nat) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false
private abbrev Plan := List (String × List Step)
private def plans : List Plan :=
  [[], [("A", [])], [("A", [(.quantity, false, 0)]), ("B", [(.quantity, true, 12)])],
   [("A", [(.quantity, true, 10)]), ("A", [(.quantity, false, 0)]), ("A", [(.quantity, true, 20)])],
   [("Outside", [(.flag, true, 1)]), ("Right", [(.bound, true, 0)])],
   [("B", [(.flag, false, 0), (.quantity, true, 8)]), ("Left", [(.bound, true, 0)])],
   [("A", [(.quantity, true, 9)]), ("Missing", []), ("LaterMissing", [])],
   [("Missing", [(.flag, true, 1)]), ("A", [(.quantity, false, 0)])]]
private def oracle (mask : Nat) (order : List String) (plan : Plan)
    (keys : List Capability) (c : Nat) : Except Capability (List Nat) := do
  let mut output := []
  for key in keys do
    let mut selected := none
    for source in order do
      let mut value := if available mask source key then some (match key with
        | .quantity => c + (if source == "A" then 1 else if source == "B" then 2 else 3)
        | .flag => if source == "Left" || c % 2 == 0 then 1 else 0
        | .bound => 1) else none
      for (name, recipe) in plan do
        for step in recipe do
          if source == name && key == step.1 then
            value := if step.2.1 then some (match key with
              | .quantity => c + step.2.2 | .flag => step.2.2 % 2 | .bound => 1) else none
      if selected.isNone then selected := value
    let some value := selected | throw key
    output := output ++ [value]
  return output
private def lists : List (List Capability) :=
  [[], [.quantity], [.flag], [.bound], [.quantity, .flag, .bound],
   [.bound, .flag, .quantity], [.quantity, .quantity], [.flag, .quantity, .flag]]
#eval do
  IO.println "FUNCTIONAL-INDEXED-REGISTRY-START"
  let mut batches := 0
  let mut rejected := 0
  let mut queries := 0
  let mut negative := 0
  let names := ["A", "B", "Left", "Right", "Outside"]
  for rows in [[["A", "B"]], [["B", "A"]], [["A"], ["B"]], [[], ["A", "B"], []]] do
    let graph : Graph := {nodes := [{name := "A"}, {name := "B"}, {name := "Outside"},
      {name := "Left", parentOrders := rows}, {name := "Right", parentOrders := rows.map List.reverse}]}
    let .ok left := linearizeVerified graph "Left" | throw (IO.userError "left rejected")
    let .ok right := linearizeVerified graph "Right" | throw (IO.userError "right rejected")
    let indices : List (Σ root : String, AncestryIndex graph root) :=
      [⟨"Left", left.indexAncestors⟩, ⟨"Right", right.indexAncestors⟩]
    for mask in List.range 8 do
      let original := ProviderRegistry.ofGraph graph (providers mask)
      let initial := IndexedRegistry.ofRegistry original
      for plan in plans do
        let mut registry := initial
        let mut ordinary := original
        let mut history : Plan := []
        for (name, recipe) in plan do
          let saved := registry
          match registry.patchBatch name (edits recipe) with
          | .error error =>
            unless error == name && !names.contains name do throw (IO.userError "wrong name error")
            rejected := rejected + 1
            break
          | .ok updated =>
            let .ok reference := ordinary.patchBatch name (edits recipe) | throw (IO.userError "ordinary disagreement")
            let next := history ++ [(name, recipe)]
            for target in names ++ ["Missing"] do
              unless updated.entries.contains target == initial.entries.contains target do
                throw (IO.userError "name membership changed")
              for keys in lists do
                for c in [0, 7] do
                  let beforeBase := (initial.entries[target]?).map (fun (state : IndexedOverlay Nat Capability Value) => observe state.base keys c)
                  let afterBase := (updated.entries[target]?).map (fun (state : IndexedOverlay Nat Capability Value) => observe state.base keys c)
                  unless (match beforeBase, afterBase with
                    | none, none => true | some a, some b => same a b | _, _ => false) do
                    throw (IO.userError "original base changed")
              if let some state := updated.entries[target]? then
                unless state.overrides.size ≤ 3 do throw (IO.userError "edit history grew stored key count")
            for packed in indices do
              for keys in lists do
                let candidate := Requirements.batchMayAffect packed.2 keys name (edits recipe)
                let expected := (name == "A" || name == "B" || name == packed.1) && recipe.any (fun step => keys.contains step.1)
                unless candidate == expected do throw (IO.userError "read scope mismatch")
                for c in [0, 7] do
                  let before := observe (assemble packed.2.order saved.dictionary) keys c
                  let after := observe (assemble packed.2.order updated.dictionary) keys c
                  unless same before (oracle mask packed.2.order.output history keys c) &&
                      same after (oracle mask packed.2.order.output next keys c) &&
                      same after (observe (assemble packed.2.order reference.dictionary) keys c) &&
                      same after (observe (assemble packed.2.order updated.snapshot.dictionary) keys c) do
                    throw (IO.userError "oracle/snapshot/ordinary agreement failed")
                  unless candidate || same before after do throw (IO.userError "negative scope changed consumer")
                if !candidate then negative := negative + 1
                queries := queries + 1
            registry := updated
            ordinary := reference
            history := next
            batches := batches + 1
        for packed in indices do
          for keys in lists do
            for c in [0, 7] do
              unless same (observe (assemble packed.2.order registry.dictionary) keys c)
                  (oracle mask packed.2.order.output history keys c) &&
                  same (observe (assemble packed.2.order initial.dictionary) keys c)
                  (oracle mask packed.2.order.output [] keys c) do
                throw (IO.userError "error or update corrupted retained snapshot")
      IO.println s!"FUNCTIONAL-INDEXED-REGISTRY-PROGRESS batches={batches} rejected={rejected}"
  unless batches == 352 && rejected == 64 && queries == 5632 && negative == 3136 do
    throw (IO.userError "unexpected indexed registry corpus")
  IO.println s!"FUNCTIONAL-INDEXED-REGISTRY-OK batches={batches} rejected={rejected} queries={queries} negative={negative} contexts=2"
#print axioms IndexedRegistry.snapshot_dictionary
#print axioms IndexedRegistry.ofRegistry_dictionary
#print axioms IndexedRegistry.patchBatch_missing
#print axioms IndexedRegistry.patchBatch_at
#print axioms IndexedRegistry.patchBatch_other
#print axioms IndexedRegistry.patchBatch_base
#print axioms IndexedRegistry.patchBatch_scope
#print axioms IndexedRegistry.patchBatch_agreement
#print axioms Requirements.prepare_indexedRegistry_of_unaffected
end LeanPoo.Tests.FunctionalIndexedRegistry
