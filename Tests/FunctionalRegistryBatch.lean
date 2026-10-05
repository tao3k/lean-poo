import LeanPoo.Functional.RegistryBatch

namespace LeanPoo.Tests.FunctionalRegistryBatch
open C4 Functional
universe u v w x

example {Context : Type u} {Key : Type v} [DecidableEq Key] {Value : Context → Key → Type w}
    {Result : Type x} (index : AncestryIndex graph root)
    (registry updated : ProviderRegistry Context Key Value) (name : String)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (applied : registry.patchBatch name edits = .ok updated)
    (unaffected : Requirements.batchMayAffect index keys name edits = false)
    (consume : Requirements.Factories Context Value keys → Result) (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble index.order registry.dictionary) keys).map consume)) :
    Claim ((Requirements.prepare (assemble index.order updated.dictionary) keys).map consume) := by
  rw [Requirements.prepare_patchBatch_of_unaffected index registry name edits keys applied unaffected]
  exact known

private inductive Capability where
  | quantity | flag | bound
  deriving BEq, DecidableEq
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
private def recipes : List (List Step) :=
  [[], [(.quantity, false, 0)], [(.quantity, true, 10), (.quantity, false, 0), (.quantity, true, 20)],
   [(.flag, true, 1)], [(.quantity, true, 8), (.flag, false, 0), (.bound, true, 0)],
   (List.range 256).map (fun step => (.quantity, true, step + 1))]
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
private def cell (mask : Nat) (source changed : String) (recipe : List Step) (key : Capability) (c : Nat) : Option Nat :=
  let original := if available mask source key then some (match key with
    | .quantity => c + (if source == "A" then 1 else if source == "B" then 2 else 3)
    | .flag => if source == "Left" || c % 2 == 0 then 1 else 0
    | .bound => 1) else none
  recipe.foldl (fun value step => if source == changed && key == step.1 then
    if step.2.1 then some (match key with
      | .quantity => c + step.2.2 | .flag => step.2.2 % 2 | .bound => 1) else none
    else value) original
private def oracle (mask : Nat) (order : List String) (name : String) (recipe : List Step)
    (keys : List Capability) (c : Nat) : Except Capability (List Nat) := do
  let mut output := []
  for key in keys do
    let mut selected := none
    for source in order do
      if selected.isNone then selected := cell mask source name recipe key c
    let some value := selected | throw key
    output := output ++ [value]
  return output
private def lists : List (List Capability) :=
  [[], [.quantity], [.flag], [.bound], [.quantity, .flag, .bound],
   [.bound, .flag, .quantity], [.quantity, .quantity], [.flag, .quantity, .flag]]

#eval do
  IO.println "FUNCTIONAL-REGISTRY-BATCH-START"
  let mut batches := 0
  let mut queries := 0
  let mut negative := 0
  let mut candidates := 0
  let mut rejected := 0
  let names := ["A", "B", "Left", "Right", "Outside"]
  for rows in [[["A", "B"]], [["B", "A"]], [["A"], ["B"]], [[], ["A", "B"], []]] do
    let graph : Graph := {nodes := [{name := "A"}, {name := "B"}, {name := "Outside"},
      {name := "Left", parentOrders := rows}, {name := "Right", parentOrders := rows.map List.reverse}]}
    let .ok left := linearizeVerified graph "Left" | throw (IO.userError "left root rejected")
    let .ok right := linearizeVerified graph "Right" | throw (IO.userError "right root rejected")
    let indices : List (Σ root : String, AncestryIndex graph root) :=
      [⟨"Left", left.indexAncestors⟩, ⟨"Right", right.indexAncestors⟩]
    for mask in List.range 8 do
      let registry := ProviderRegistry.ofGraph graph (providers mask)
      for recipe in recipes do
        match registry.patchBatch "Missing" (edits recipe) with
        | .error name => unless name == "Missing" do throw (IO.userError "wrong unknown-name error")
        | .ok _ => throw (IO.userError "batch registered an unknown provider")
        rejected := rejected + 1
        for name in names do
          let .ok updated := registry.patchBatch name (edits recipe) | throw (IO.userError "known name rejected")
          for target in names ++ ["Missing"] do
            unless updated.entries.contains target == registry.entries.contains target do
              throw (IO.userError "provider-name scope changed")
          for packed in indices do
            for keys in lists do
              let candidate := Requirements.batchMayAffect packed.2 keys name (edits recipe)
              let expected := (name == "A" || name == "B" || name == packed.1) && recipe.any (fun step => keys.contains step.1)
              unless candidate == expected do throw (IO.userError "batch impact mismatch")
              for c in [0, 7] do
                let before := observe (assemble packed.2.order registry.dictionary) keys c
                let after := observe (assemble packed.2.order updated.dictionary) keys c
                unless same before (observe (assemble packed.2.order (providers mask)) keys c) do
                  throw (IO.userError "original registry snapshot changed")
                unless same after (oracle mask packed.2.order.output name recipe keys c) do
                  throw (IO.userError "batch result/first error differs from independent oracle")
                unless candidate || same before after do throw (IO.userError "negative batch impact changed consumer")
              if candidate then candidates := candidates + 1 else negative := negative + 1
              queries := queries + 1
          batches := batches + 1
      IO.println s!"FUNCTIONAL-REGISTRY-BATCH-PROGRESS batches={batches} queries={queries}"
  unless batches == 960 && queries == 15360 && rejected == 192 && negative == 10368 && candidates == 4992 do
    throw (IO.userError "unexpected batch corpus")
  IO.println s!"FUNCTIONAL-REGISTRY-BATCH-OK batches={batches} queries={queries} negative={negative} candidates={candidates} rejected={rejected} contexts=2 longestBatch=256"

#print axioms ProviderRegistry.patchBatch_missing
#print axioms ProviderRegistry.patchBatch_at
#print axioms ProviderRegistry.patchBatch_other
#print axioms ProviderRegistry.patchBatch_dictionary
#print axioms ProviderRegistry.patchBatch_nil
#print axioms ProviderRegistry.patchBatch_scope
#print axioms ProviderRegistry.patchBatch_untouched
#print axioms Requirements.prepare_patchBatch_stable
#print axioms Requirements.batchMayAffect_iff
#print axioms Requirements.prepare_patchBatch_of_unaffected
end LeanPoo.Tests.FunctionalRegistryBatch
