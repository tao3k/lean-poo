import LeanPoo.Functional.RegistryPatch

namespace LeanPoo.Tests.FunctionalRegistryPatch
open C4 Functional
universe u v w x

example {Context : Type u} {Key : Type v} [DecidableEq Key] {Value : Context → Key → Type w}
    {Result : Type x} (index : AncestryIndex graph root)
    (registry updated : ProviderRegistry Context Key Value) (name : String) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) (keys : List Key)
    (applied : registry.patch name key replacement = .ok updated)
    (unaffected : Requirements.mayAffect index keys name key = false)
    (consume : Requirements.Factories Context Value keys → Result) (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble index.order registry.dictionary) keys).map consume)) :
    Claim ((Requirements.prepare (assemble index.order updated.dictionary) keys).map consume) := by
  rw [Requirements.prepare_patch_of_unaffected index registry name key replacement keys applied unaffected]
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
  | .flag => if available mask name .flag then
      some (fun c => if name == "Left" then true else c % 2 == 0) else none
  | .bound => if available mask name .bound then some (Factory.fromProof (fun _ => by omega)) else none
private def replacement (provided : Bool) : (key : Capability) →
    Option (Factory Nat (fun c => Value c key))
  | .quantity => if provided then some (fun c => ⟨c + 10, by omega⟩) else none
  | .flag => if provided then some (fun _ => true) else none
  | .bound => if provided then some (Factory.fromProof (fun _ => by omega)) else none
private def lists : List (List Capability) :=
  [[], [.quantity], [.flag], [.bound], [.quantity, .flag, .bound],
   [.bound, .flag, .quantity], [.quantity, .quantity], [.flag, .quantity]]
private def encode (c : Nat) : (keys : List Capability) → Requirements.Results Value c keys → List Nat
  | [], _ => []
  | .quantity :: rest, (value, tail) => value.val :: encode c rest tail
  | .flag :: rest, (value, tail) => Bool.toNat value :: encode c rest tail
  | .bound :: rest, (_, tail) => 1 :: encode c rest tail
private def observe (provider : Provider Nat Capability Value) (keys : List Capability) (c : Nat) :=
  (Requirements.prepare provider keys).map (fun retained => encode c keys (Requirements.build retained c))
private def sameResults : Except Capability (List Nat) → Except Capability (List Nat) → Bool
  | .error a, .error b => a == b
  | .ok a, .ok b => a == b
  | _, _ => false
-- Independent availability/value oracle, including override precedence and removals.
private def oracle (mask : Nat) (names : List String) (name : String) (edited : Capability)
    (provided : Bool) (keys : List Capability) (c : Nat) : Except Capability (List Nat) := do
  let mut values := []
  for key in keys do
    let candidate := names.find? fun source =>
      if source == name && key == edited then provided else available mask source key
    let some source := candidate | throw key
    let value := if source == name && key == edited then
      match key with | .quantity => c + 10 | .flag | .bound => 1
    else match key with
      | .quantity => c + (if source == "A" then 1 else if source == "B" then 2 else 3)
      | .flag => if source == "Left" || c % 2 == 0 then 1 else 0
      | .bound => 1
    values := values ++ [value]
  return values

#eval do
  IO.println "FUNCTIONAL-REGISTRY-PATCH-START"
  let mut patches := 0
  let mut queries := 0
  let mut unaffected := 0
  let mut affected := 0
  let mut rejected := 0
  let mut observedChanges := 0
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
      for key in [Capability.quantity, .flag, .bound] do
        for provided in [false, true] do
          match registry.patch "Missing" key (replacement provided key) with
          | .error name => unless name == "Missing" do throw (IO.userError "wrong unknown provider error")
          | .ok _ => throw (IO.userError "patch registered an unknown name")
          rejected := rejected + 1
          for name in names do
            let .ok updated := registry.patch name key (replacement provided key) |
              throw (IO.userError "declared provider rejected")
            for target in names ++ ["Missing"] do
              unless updated.entries.contains target == registry.entries.contains target do
                throw (IO.userError "provider-name scope changed")
            for packed in indices do
              let index := packed.2
              for keys in lists do
                let candidate := Requirements.mayAffect index keys name key
                let expected := (name == "A" || name == "B" || name == packed.1) && keys.contains key
                unless candidate == expected do throw (IO.userError "candidate impact query incorrect")
                let mut changed := false
                for c in [0, 7] do
                  let before := observe (assemble index.order registry.dictionary) keys c
                  let after := observe (assemble index.order updated.dictionary) keys c
                  unless sameResults after (oracle mask index.order.output name key provided keys c) do
                    throw (IO.userError "edited result/first-error differs from oracle")
                  unless sameResults before (observe (assemble index.order (providers mask)) keys c) do
                    throw (IO.userError "old registry snapshot changed")
                  if !candidate then
                    unless sameResults before after do throw (IO.userError "negative impact query changed consumer")
                  if !(sameResults before after) then changed := true
                if candidate then affected := affected + 1 else unaffected := unaffected + 1
                if changed then observedChanges := observedChanges + 1
                queries := queries + 1
            patches := patches + 1
      IO.println s!"FUNCTIONAL-REGISTRY-PATCH-PROGRESS patches={patches} queries={queries}"
  unless patches == 960 && queries == 15360 && rejected == 192 &&
      unaffected > 0 && affected > observedChanges && observedChanges > 0 do
    throw (IO.userError "unexpected patch corpus/candidate boundary")
  -- Explicit false-positive: A shadows a changed B for the same requested key.
  let graph : Graph := {nodes := [{name := "A"}, {name := "B"}, {name := "Root", parentOrders := [["A", "B"]]}]}
  let .ok order := linearizeVerified graph "Root" | throw (IO.userError "shadow graph rejected")
  let registry := ProviderRegistry.ofGraph graph (providers 1)
  let .ok updated := registry.patch "B" .quantity (replacement true .quantity) | throw (IO.userError "B patch failed")
  unless Requirements.mayAffect order.indexAncestors [Capability.quantity] "B" .quantity &&
      sameResults (observe (assemble order registry.dictionary) [.quantity] 7)
        (observe (assemble order updated.dictionary) [.quantity] 7) do
    throw (IO.userError "candidate impact incorrectly means actual change")
  IO.println s!"FUNCTIONAL-REGISTRY-PATCH-OK patches={patches} queries={queries} unaffected={unaffected} candidates={affected} observedChanges={observedChanges} rejected={rejected} contexts=2"

#print axioms ProviderRegistry.patch_missing
#print axioms ProviderRegistry.patch_at
#print axioms ProviderRegistry.patch_other
#print axioms ProviderRegistry.patch_scope
#print axioms assemble_patch_stable
#print axioms Requirements.prepare_patch_stable
#print axioms Requirements.mayAffect_iff
#print axioms Requirements.prepare_patch_of_unaffected
end LeanPoo.Tests.FunctionalRegistryPatch
