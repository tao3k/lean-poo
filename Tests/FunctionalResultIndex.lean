import LeanPoo.Functional.ResultIndex

namespace LeanPoo.Tests.FunctionalResultIndex
open Functional Requirements
private inductive Key where
  | quantity | flag | proof | missing
  deriving BEq, DecidableEq, ReflBEq, LawfulBEq
private instance : Hashable Key where
  hash _ := 0
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .proof => PLift (c ≤ c+2)
  | .missing => Nat
private def data (c : Nat) : (keys : List Key) → Nat → Results Value c keys
  | [], _ => PUnit.unit
  | key :: rest, position => ((match key with
      | .quantity => ⟨c+position, by omega⟩
      | .flag => position % 2 == 0
      | .proof => ⟨by omega⟩
      | .missing => (999 : Nat)), data c rest (position+1))
private def scalar (c : Nat) : (key : Key) → Value c key → Nat
  | .quantity, value => value.val
  | .flag, value => cond value (1 : Nat) (0 : Nat)
  | .proof, _ => 1
  | .missing, value => value
private def flatten (c : Nat) : {keys : List Key} → Results Value c keys → List Nat
  | [], _ => []
  | key :: _, (value, rest) => scalar c key value :: flatten c rest
private def requests (mask : Nat) := [Key.quantity,.flag,.proof].zipIdx.filterMap
  (fun (key, index) => if mask / 2^index % 2 == 1 then some key else none)
private def orders (keys : List Key) := [keys,keys.reverse,keys++keys]
private def oracle (c : Nat) (keys : List Key) (key : Key) : Option Nat :=
  (keys.zipIdx.find? (fun pair => pair.1 == key)).map fun (_, position) => match key with
    | .quantity => c+position
    | .flag => if position % 2 == 0 then 1 else 0
    | .proof => 1
    | .missing => 999
private def run : IO Unit := do
  let mut indices := 0
  let mut queries := 0
  let mut cases := 0
  let mut positions := 0
  for sourceMask in List.range 8 do
    for source in orders (requests sourceMask) do
      for c in [0,7,23] do
        let built := data c source 0
        let index := ResultIndex.ofResults built
        indices := indices+1
        for key in [Key.quantity,.flag,.proof,.missing] do
          unless (index.find? key).map (scalar c key) == oracle c source key do
            throw (IO.userError "collision-safe lookup differs from first-occurrence oracle")
          if member : key ∈ source then
            unless some (scalar c key (index.get key member)) == oracle c source key do
              throw (IO.userError "typed lookup differs from independent value")
          queries := queries+1
        for mask in List.range 8 do
          for target in orders (requests mask) do
            if included : ∀ key ∈ target, key ∈ source then
              let actual := flatten c (index.project target included)
              let expected := target.filterMap (oracle c source)
              unless actual == expected && actual == flatten c (projectResults built target included) do
                throw (IO.userError "retained indexed projection differs from scalar/list controls")
              cases := cases+1
              positions := positions+target.length
  unless indices == 72 && queries == 288 && cases == 729 && positions == 972 do
    throw (IO.userError "result-index coverage drift")
  IO.println s!"FUNCTIONAL-RESULT-INDEX-OK indices={indices} queries={queries} projections={cases} positions={positions} contexts=3 forcedCollisions=true"
#eval run

-- Proof transport preserves joint client properties without exposing hash internals.
example {C K : Type} {V : C → K → Type} [BEq K] [Hashable K] [LawfulBEq K] [DecidableEq K]
    {c : C} {source : List K} (built : Results V c source) (index : ResultIndex built)
    (target : List K) (included : ∀ k ∈ target, k ∈ source)
    (Claim : Results V c target → Prop) (known : Claim (projectResults built target included)) :
    Claim (index.project target included) := by
  rw [ResultIndex.project_eq]; exact known
example : True := by
  fail_if_success have changed : ResultIndex (data 0 [.quantity] 1) := ResultIndex.ofResults (data 0 [.quantity] 0)
  fail_if_success have wrong : ResultIndex (data 9 [.quantity] 0) := ResultIndex.ofResults (data 0 [.quantity] 0)
  trivial
#print axioms ResultIndex.find?_present
#print axioms ResultIndex.find?_absent
#print axioms ResultIndex.get_eq
#print axioms ResultIndex.project_eq
end LeanPoo.Tests.FunctionalResultIndex
