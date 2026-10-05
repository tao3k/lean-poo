import LeanPoo.Functional.IndexedTransaction
namespace LeanPoo.Tests.FunctionalIndexedTransaction
open C4 Functional
universe u v w x
example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] {Value : Context → Key → Type w}
    {Result : Type x} (index : AncestryIndex graph root)
    (registry updated : IndexedRegistry Context Key Value)
    (changes : List (RegistryEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchTransaction changes = .ok updated)
    (unaffected : Requirements.transactionMayAffect index keys changes = false)
    (consume : Requirements.Factories Context Value keys → Result) (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble index.order registry.dictionary) keys).map consume)) :
    Claim ((Requirements.prepare (assemble index.order updated.dictionary) keys).map consume) := by
  rw [Requirements.prepare_indexedTransaction_of_unaffected index registry changes keys applied unaffected]
  exact known
-- Representation migration transfers the complete consumer result, even when
-- edits affect its requested keys, without a negative-scope premise.
example {Context : Type u} {Key : Type v}
    [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]
    {Value : Context → Key → Type w} {Result : Type x}
    (index : AncestryIndex graph root) (registry : ProviderRegistry Context Key Value)
    (changes : List (RegistryEdit Context Key Value)) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except String (Except Key Result) → Prop)
    (known : Claim ((registry.patchTransaction changes).map (fun updated =>
      (Requirements.prepare (assemble index.order updated.dictionary) keys).map consume))) :
    Claim (((IndexedRegistry.ofRegistry registry).patchTransaction changes).map (fun updated =>
      (Requirements.prepare (assemble index.order updated.dictionary) keys).map consume)) := by
  rw [IndexedRegistry.ofRegistry_transaction_consumer registry changes
    (fun dictionary => (Requirements.prepare (assemble index.order dictionary) keys).map consume)]
  exact known
private inductive Capability where
  | quantity | flag | bound
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq
private instance : Hashable Capability where
  hash _ := 0
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
private def changes (plan : Plan) : List (RegistryEdit Nat Capability Value) :=
  plan.map (fun entry => (entry.1, edits entry.2))
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
  IO.println "FUNCTIONAL-INDEXED-TRANSACTION-START"
  let mut successes := 0
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
      let ordinary := ProviderRegistry.ofGraph graph (providers mask)
      let registry := IndexedRegistry.ofRegistry ordinary
      for plan in plans do
        let firstMissing := plan.find? (fun (entry : String × List Step) => !names.contains entry.1)
        match registry.patchTransaction (changes plan) with
        | .error name =>
          let .error referenceName := ordinary.patchTransaction (changes plan) |
            throw (IO.userError "ordinary transaction unexpectedly succeeded")
          unless name == referenceName do throw (IO.userError "ordinary first-error mismatch")
          unless firstMissing.map Prod.fst == some name do throw (IO.userError "wrong first unknown name")
          rejected := rejected + 1
        | .ok updated =>
          unless firstMissing.isNone do throw (IO.userError "partial transaction escaped")
          let .ok reference := ordinary.patchTransaction (changes plan) | throw (IO.userError "ordinary transaction rejected")
          for target in names ++ ["Missing", "LaterMissing"] do
            unless updated.entries.contains target == registry.entries.contains target do
              throw (IO.userError "transaction changed name scope")
            for key in ([.quantity, .flag, .bound] : List Capability) do
              for c in [0, 7] do
                let baseBefore := (registry.entries[target]?).map (fun state : IndexedOverlay Nat Capability Value => observe state.base [key] c)
                let baseAfter := (updated.entries[target]?).map (fun state : IndexedOverlay Nat Capability Value => observe state.base [key] c)
                unless (match baseBefore, baseAfter with
                  | none, none => true
                  | some a, some b => same a b
                  | _, _ => false) do throw (IO.userError "transaction changed base")
          for packed in indices do
            for keys in lists do
              let candidate := Requirements.transactionMayAffect packed.2 keys (changes plan)
              let expected := plan.any (fun (name, recipe) =>
                (name == "A" || name == "B" || name == packed.1) && recipe.any (fun step => keys.contains step.1))
              unless candidate == expected do throw (IO.userError "transaction impact mismatch")
              for c in [0, 7] do
                let before := observe (assemble packed.2.order registry.dictionary) keys c
                let after := observe (assemble packed.2.order updated.dictionary) keys c
                unless same after (observe (assemble packed.2.order reference.dictionary) keys c) do
                  throw (IO.userError "ordinary transaction mismatch")
                unless same after (oracle mask packed.2.order.output plan keys c) do
                  throw (IO.userError "transaction/first capability error oracle mismatch")
                unless candidate || same before after do throw (IO.userError "negative scope changed")
              if !candidate then negative := negative + 1
              queries := queries + 1
          successes := successes + 1
        -- Check retained snapshot after failures too, including failures after a valid prefix.
        for packed in indices do
          for keys in lists do
            for c in [0, 7] do
              unless same (observe (assemble packed.2.order registry.dictionary) keys c)
                  (oracle mask packed.2.order.output [] keys c) do
                throw (IO.userError "original snapshot changed")
      IO.println s!"FUNCTIONAL-INDEXED-TRANSACTION-PROGRESS successes={successes} rejected={rejected}"
  unless successes == 192 && rejected == 64 && queries == 3072 && negative == 1920 do
    throw (IO.userError "unexpected transaction corpus")
  IO.println s!"FUNCTIONAL-INDEXED-TRANSACTION-OK successes={successes} rejected={rejected} queries={queries} negative={negative} contexts=2"
private def scopeAbsent : ProviderRegistry Nat Capability Value := ⟨{}⟩
private def scopeRegistered : ProviderRegistry Nat Capability Value :=
  ⟨scopeAbsent.entries.insert "Empty" (fun _ => none)⟩
example : (IndexedRegistry.ofRegistry scopeRegistered).dictionary = scopeAbsent.dictionary := by
  rw [IndexedRegistry.ofRegistry_dictionary]
  funext name key
  by_cases same : "Empty" = name <;>
    simp [scopeRegistered, scopeAbsent, ProviderRegistry.dictionary, same]

-- Dictionary equality does not imply equal transaction errors: a registered
-- empty provider is different from an unknown name. Guard against dropping scope.
#eval do
  let absent := scopeAbsent
  let registered := scopeRegistered
  let indexed := IndexedRegistry.ofRegistry registered
  for name in ["Empty", "Missing"] do
    for key in ([.quantity, .flag, .bound] : List Capability) do
      for c in [0, 7] do
        unless same (observe (indexed.dictionary name) [key] c)
            (observe (absent.dictionary name) [key] c) do
          throw (IO.userError "empty-provider dictionary control differs")
  unless indexed.entries.contains "Empty" && !absent.entries.contains "Empty" do
    throw (IO.userError "name scope counterexample missing")
  let edits : List (RegistryEdit Nat Capability Value) := [("Empty", [])]
  let .ok _ := indexed.patchTransaction edits | throw (IO.userError "registered empty name rejected")
  let .error name := absent.patchTransaction edits | throw (IO.userError "unknown empty name accepted")
  unless name == "Empty" do throw (IO.userError "wrong empty-name error")
  IO.println "FUNCTIONAL-INDEXED-TRANSACTION-EMPTY-SCOPE-OK dictionary_cells=12"
#print axioms IndexedRegistry.patchTransaction_nil
#print axioms IndexedRegistry.patchTransaction_cons
#print axioms IndexedRegistry.patchTransaction_missing
#print axioms IndexedRegistry.patchTransaction_scope
#print axioms IndexedRegistry.patchTransaction_base
#print axioms Requirements.prepare_indexedTransaction_of_unaffected
#print axioms IndexedRegistry.patchTransaction_congr
#print axioms IndexedRegistry.ofRegistry_patchTransaction
#print axioms IndexedRegistry.ofRegistry_transaction_consumer
end LeanPoo.Tests.FunctionalIndexedTransaction
