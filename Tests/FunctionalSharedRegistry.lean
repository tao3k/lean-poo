import LeanPoo.Functional.SharedRegistry

namespace LeanPoo.Tests.FunctionalSharedRegistry
open C4 Functional
variable {graph other : Graph}
universe u v w x

-- One shared table, arbitrary consumer and claim, with no per-root alignment lemma.
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble order providers) keys).map consume)) :
    Claim ((Requirements.prepare (assemble order (ProviderRegistry.ofGraph graph providers).dictionary)
      keys).map consume) := by
  rw [Requirements.prepare_ofGraph_registry]
  exact known

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root) (change : graph.Relabeling other)
    (unique : (graph.nodes.map Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble order providers) keys).map consume)) :
    Claim ((Requirements.prepare (assemble (order.relabel change unique)
      (ProviderRegistry.relabelGraph change providers).dictionary) keys).map consume) := by
  rw [Requirements.prepare_relabelGraph_registry]
  exact known

private def prefixed (name : String) := "模块::" ++ name
private theorem prefixed_injective : Function.Injective prefixed := by
  intro a b same
  exact (String.append_right_inj "模块::").mp same
private def swap (name : String) : String :=
  if name = "A" then "B" else if name = "B" then "A" else name
private theorem swap_twice (name : String) : swap (swap name) = name := by
  by_cases a : name = "A"
  · subst name; decide
  · by_cases b : name = "B"
    · subst name; decide
    · simp [swap, a, b]
private theorem swap_injective : Function.Injective swap := by
  intro a b same
  have twice := congrArg swap same
  simpa only [swap_twice] using twice

private inductive Capability where
  | quantity | flag | bound | unrelated
  deriving BEq, DecidableEq
private def Value (context : Nat) : Capability → Type
  | .quantity => {n : Nat // context ≤ n}
  | .flag | .unrelated => Bool
  | .bound => PLift (context ≤ context + 1)
private def available (mask : Nat) : Capability → Bool
  | .quantity => mask % 2 == 1
  | .flag => mask / 2 % 2 == 1
  | .bound => mask / 4 % 2 == 1
  | .unrelated => false
private def providers (mask : Nat) (name : String) : Provider Nat Capability Value
  | .quantity => if available mask .quantity && (name == "A" || name == "B") then
      some (fun c => ⟨c + (if name == "A" then 1 else 2), by omega⟩) else none
  | .flag => if available mask .flag && (name == "Left" || name == "B") then
      some (fun c => if name == "Left" then true else c % 2 == 0) else none
  | .bound => if available mask .bound && name == "A" then
      some (Factory.fromProof (fun _ => by omega)) else none
  | .unrelated => if name == "Outside" || name == "Undeclared" then some (fun _ => true) else none
private def lists : List (List Capability) :=
  [[], [.quantity], [.flag], [.bound], [.quantity, .flag, .bound],
   [.bound, .flag, .quantity], [.quantity, .quantity], [.unrelated, .quantity], [.quantity, .unrelated]]
private def encode (context : Nat) : (keys : List Capability) →
    Requirements.Results Value context keys → List Nat
  | [], _ => []
  | .quantity :: rest, (value, tail) => value.val :: encode context rest tail
  | .flag :: rest, (value, tail) => Bool.toNat value :: encode context rest tail
  | .unrelated :: rest, (value, tail) => Bool.toNat value :: encode context rest tail
  | .bound :: rest, (_, tail) => 1 :: encode context rest tail

private def compare (mask : Nat) (original shared : Provider Nat Capability Value) : IO Nat := do
  let mut successful := 0
  for keys in lists do
    let expected := keys.find? fun key => !(available mask key)
    match Requirements.prepare original keys, Requirements.prepare shared keys, expected with
    | .error a, .error b, some missing =>
      unless a == missing && b == missing do throw (IO.userError "first missing capability changed")
    | .ok old, .ok retained, none =>
      for context in [0, 7] do
        unless encode context keys (Requirements.build old context) ==
            encode context keys (Requirements.build retained context) do
          throw (IO.userError "dependent shared factory changed")
      successful := successful + 1
    | _, _, _ => throw (IO.userError "shared availability changed")
  return successful

#eval do
  IO.println "FUNCTIONAL-SHARED-REGISTRY-START"
  let mut registries := 0
  let mut preparations := 0
  let mut successful := 0
  for rows in [[["A", "B"]], [["B", "A"]], [["A"], ["B"]], [[], ["A", "B"], []]] do
    let graph : Graph := {nodes := [{name := "A"}, {name := "B"}, {name := "Outside"},
      {name := "Left", parentOrders := rows},
      {name := "Right", parentOrders := rows.map List.reverse}]}
    have unique : (graph.nodes.map Node.name).Nodup := by
      change ["A", "B", "Outside", "Left", "Right"].Nodup
      decide
    let .ok left := linearizeVerified graph "Left" | throw (IO.userError "left root rejected")
    let .ok right := linearizeVerified graph "Right" | throw (IO.userError "right root rejected")
    for mask in List.range 8 do
      let shared := ProviderRegistry.ofGraph graph (providers mask)
      unless (shared.dictionary "Outside" .unrelated).isSome &&
          (shared.dictionary "Undeclared" .unrelated).isNone do
        throw (IO.userError "declaration scope changed")
      successful := successful + (← compare mask (assemble left (providers mask)) (assemble left shared.dictionary))
      successful := successful + (← compare mask (assemble right (providers mask)) (assemble right shared.dictionary))
      preparations := preparations + 2 * lists.length
      registries := registries + 1
      for transform in [(⟨prefixed, prefixed_injective⟩ : {f : String → String // Function.Injective f}),
          ⟨swap, swap_injective⟩] do
        let other : Graph := {nodes := (graph.rename transform.val).nodes.reverse}
        let change : graph.Relabeling other := ⟨transform.val, transform.property, (List.reverse_perm _).symm⟩
        let migrated := ProviderRegistry.relabelGraph change (providers mask)
        unless (migrated.dictionary (change.rename "Outside") .unrelated).isSome &&
            (migrated.dictionary (change.rename "Undeclared") .unrelated).isNone do
          throw (IO.userError "mapped declaration scope changed")
        successful := successful + (← compare mask (assemble left (providers mask))
          (assemble (left.relabel change unique) migrated.dictionary))
        successful := successful + (← compare mask (assemble right (providers mask))
          (assemble (right.relabel change unique) migrated.dictionary))
        preparations := preparations + 2 * lists.length
        registries := registries + 1
      if registries % 24 == 0 then
        IO.println s!"FUNCTIONAL-SHARED-REGISTRY-PROGRESS registries={registries} preparations={preparations}"
  unless registries == 96 && preparations == 1728 && successful > 0 && successful < preparations do
    throw (IO.userError "unexpected shared registry corpus size")
  IO.println s!"FUNCTIONAL-SHARED-REGISTRY-OK registries={registries} preparations={preparations} successful={successful} contexts=2 roots=2"

#print axioms ProviderRegistry.ofGraph_lookup
#print axioms ProviderRegistry.ofGraph_missing
#print axioms assemble_ofGraph_registry
#print axioms Requirements.prepare_ofGraph_registry
#print axioms ProviderRegistry.relabelGraph_lookup
#print axioms ProviderRegistry.relabelGraph_missing
#print axioms ProviderRegistry.relabelGraph_relabel
#print axioms assemble_relabelGraph_registry
#print axioms Requirements.prepare_relabelGraph_registry
end LeanPoo.Tests.FunctionalSharedRegistry
