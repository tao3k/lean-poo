import LeanPoo.Functional.Registry

namespace LeanPoo.Tests.FunctionalRegistry
open C4 Functional
variable {graph other : Graph}
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


universe u v w x
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root) (change : graph.Relabeling other)
    (unique : (graph.nodes.map Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble order providers) keys).map consume)) :
    Claim ((Requirements.prepare (assemble (order.relabel change unique)
      (ProviderRegistry.relabel order change providers).dictionary) keys).map consume) := by
  rw [Requirements.prepare_relabel_registry]
  exact known

private inductive Capability where
  | background | flag | residual
  deriving BEq, DecidableEq
private def Value (context : Nat) : Capability → Type
  | .background => {n : Nat // context ≤ n}
  | .flag => Bool
  | .residual => {n : Nat // context + 2 ≤ n}
private def available (mask : Nat) : Capability → Bool
  | .background => mask % 2 == 1
  | .flag => mask / 2 % 2 == 1
  | .residual => mask / 4 % 2 == 1
private def offset (name : String) := if name == "A" then 1 else if name == "B" then 2 else 3
private def providers (mask : Nat) (name : String) : Provider Nat Capability Value
  | .background =>
    if (available mask .background && name != "Root") || name == "Outside" then
      some (fun c => ⟨c + offset name, by omega⟩) else none
  | .flag => if available mask .flag && name == "B" then some (fun c => c % 2 == 0) else none
  | .residual => if available mask .residual && (name == "A" || name == "B") then
      some (fun c => ⟨c + 2 + offset name, by omega⟩) else none
private def lists : List (List Capability) :=
  [[], [.background], [.flag], [.residual], [.background, .flag, .residual],
   [.residual, .flag, .background], [.residual, .background], [.residual, .residual]]
private def encode (context : Nat) : (keys : List Capability) →
    Requirements.Results Value context keys → List Nat
  | [], _ => []
  | .background :: rest, (value, tail) => value.val :: encode context rest tail
  | .flag :: rest, (value, tail) => Bool.toNat value :: encode context rest tail
  | .residual :: rest, (value, tail) => value.val :: encode context rest tail

#eval do
  IO.println "FUNCTIONAL-REGISTRY-START"
  let mut registries := 0
  let mut preparations := 0
  let mut successful := 0
  for localOrders in [[["P", "B"]], [["B", "P"]], [["P"], ["B"]], [[], ["P", "B"], []]] do
    let graph : Graph := {nodes := [{name := "A"}, {name := "B"},
      {name := "P", parentOrders := [["A"]]}, {name := "Root", parentOrders := localOrders}]}
    have unique : (graph.nodes.map Node.name).Nodup := by
      change ["A", "B", "P", "Root"].Nodup
      decide
    let .ok order := linearizeVerified graph "Root" | throw (IO.userError "source graph rejected")
    for transform in [(⟨prefixed, prefixed_injective⟩ : {f : String → String // Function.Injective f}),
        ⟨swap, swap_injective⟩] do
      let other : Graph := {nodes := (graph.rename transform.val).nodes.reverse}
      let change : graph.Relabeling other := ⟨transform.val, transform.property, (List.reverse_perm _).symm⟩
      let moved := order.relabel change unique
      for mask in List.range 8 do
        let registry := ProviderRegistry.relabel order change (providers mask)
        for name in order.output do
          unless (registry.entries[change.rename name]?).isSome do
            throw (IO.userError "mapped ancestor missing from registry")
        -- An unrelated source provider exists, but it is outside this root's cut.
        unless (providers mask "Outside" .background).isSome &&
            (registry.dictionary (change.rename "Outside") .background).isNone do
          throw (IO.userError "registry escaped verified ancestor scope")
        for keys in lists do
          let original := Requirements.prepare (assemble order (providers mask)) keys
          let migrated := Requirements.prepare (assemble moved registry.dictionary) keys
          let firstMissing := keys.find? fun key => !(available mask key)
          match original, migrated, firstMissing with
          | .error a, .error b, some expected =>
            unless a == expected && b == expected do throw (IO.userError "first missing key changed")
          | .ok old, .ok retained, none =>
            for context in [0, 7] do
              unless encode context keys (Requirements.build old context) ==
                  encode context keys (Requirements.build retained context) do
                throw (IO.userError "dependent factory result changed")
            successful := successful + 1
          | _, _, _ => throw (IO.userError "availability changed")
          preparations := preparations + 1
        registries := registries + 1
        if registries % 8 == 0 then IO.println s!"FUNCTIONAL-REGISTRY-PROGRESS registries={registries} preparations={preparations}"
  unless registries == 64 && preparations == 512 && successful > 0 && successful < preparations do
    throw (IO.userError "unexpected registry corpus size")
  IO.println s!"FUNCTIONAL-REGISTRY-OK registries={registries} preparations={preparations} successful={successful} contexts=2"

#print axioms ProviderRegistry.relabel_lookup
#print axioms ProviderRegistry.relabel_aligned
#print axioms ProviderRegistry.relabel_missing
#print axioms assemble_relabel_registry
#print axioms Requirements.prepare_relabel_registry
end LeanPoo.Tests.FunctionalRegistry
