import LeanPoo.Functional.ScopedTransaction
namespace LeanPoo.Tests.FunctionalScopedTransaction
open C4 Functional
universe u v w x
example {Context : Type u} {Key : Type v}
    [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]
    {Value : Context → Key → Type w} {Result : Type x}
    (index : AncestryIndex graph root) (registry : ProviderRegistry Context Key Value)
    (changes : List (RegistryEdit Context Key Value)) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except String (Except Key Result) → Prop)
    (known : Claim ((registry.patchTransaction changes).map (fun updated =>
      (Requirements.prepare (assemble index.order updated.dictionary) keys).map consume))) :
    Claim ((Requirements.prepareTransaction index (IndexedRegistry.ofRegistry registry) changes keys).map
      (fun ready => ready.map consume)) := by
  rw [Requirements.prepareTransaction_ofRegistry]
  cases applied : registry.patchTransaction changes <;>
    simpa only [applied, Except.map] using known
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
private def observeOutcome (result : Except String (Except Capability
    (Requirements.Factories Nat Value keys))) (c : Nat) : Except String (Except Capability (List Nat)) :=
  result.map (fun ready => ready.map (fun factories => values (Requirements.build factories c)))
private def sameOutcome : Except String (Except Capability (List Nat)) →
    Except String (Except Capability (List Nat)) → Bool
  | .error a, .error b => a == b
  | .ok a, .ok b => same a b
  | _, _ => false
#eval do
  IO.println "FUNCTIONAL-SCOPED-TRANSACTION-START"
  let mut cases := 0
  let mut negative := 0
  let mut positive := 0
  let mut errors := 0
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
      let indexed := IndexedRegistry.ofRegistry ordinary
      for plan in plans do
        let edits := changes plan
        let firstMissing := plan.find? (fun (entry : String × List Step) => !names.contains entry.1)
        for packed in indices do
          for keys in lists do
            let view := Requirements.prepareTransaction packed.2 indexed edits keys
            let full := (indexed.patchTransaction edits).map (fun updated : IndexedRegistry Nat Capability Value =>
              Requirements.prepare (assemble packed.2.order updated.dictionary) keys)
            let reference := (ordinary.patchTransaction edits).map (fun updated : ProviderRegistry Nat Capability Value =>
              Requirements.prepare (assemble packed.2.order updated.dictionary) keys)
            let candidate := Requirements.transactionMayAffect packed.2 keys edits
            if candidate then positive := positive + 1 else negative := negative + 1
            for c in [0, 7] do
              let expected : Except String (Except Capability (List Nat)) := match firstMissing with
                | some missing => .error missing.1
                | none => .ok (oracle mask packed.2.order.output plan keys c)
              let actual := observeOutcome view c
              unless sameOutcome actual expected && sameOutcome actual (observeOutcome full c) &&
                  sameOutcome actual (observeOutcome reference c) do
                throw (IO.userError "scoped/full/scalar consumer outcome mismatch")
              if !candidate && firstMissing.isNone then
                unless sameOutcome actual (.ok (observe (assemble packed.2.order indexed.dictionary) keys c)) do
                  throw (IO.userError "negative branch changed retained preparation")
            if firstMissing.isSome then errors := errors + 1
            cases := cases + 1
      IO.println s!"FUNCTIONAL-SCOPED-TRANSACTION-PROGRESS cases={cases}"
  unless cases == 4096 && errors == 1024 do throw (IO.userError "unexpected scoped corpus")
  IO.println s!"FUNCTIONAL-SCOPED-TRANSACTION-OK cases={cases} negative={negative} positive={positive} name_errors={errors} contexts=2"
#print axioms Requirements.prepareTransaction_eq
#print axioms Requirements.prepareTransaction_ofRegistry
#print axioms Requirements.prepareTransaction_unaffected
end LeanPoo.Tests.FunctionalScopedTransaction
