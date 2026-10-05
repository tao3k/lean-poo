import LeanPoo.Functional.ViewComposition

namespace LeanPoo.Tests.FunctionalViewComposition
open Functional Requirements
private def Value (_ : Nat) (_ : Nat) := Nat
private def factories : (ks : List Nat) → Nat → Factories Nat Value ks
  | [], _ => PUnit.unit
  | key :: rest, index => (fun c => c+10*index+key, factories rest (index+1))
private def flatten {c : Nat} : {ks : List Nat} → Results Value c ks → List Nat
  | [], _ => []
  | _ :: _, (head, tail) => head :: flatten tail
private def requests (mask : Nat) := [0,1,2].filter (fun key => mask / 2^key % 2 == 1)
private def orders (ks : List Nat) := [ks, ks.reverse, ks ++ ks]
private def oracle (source target : List Nat) (c : Nat) : List Nat :=
  target.map fun key => match source.zipIdx.find? (fun pair => pair.1 == key) with
    | some (_, index) => c+10*index+key
    | none => 999999
private def run : IO Unit := do
  let mut cases := 0
  for sourceMask in List.range 8 do
    for source in orders (requests sourceMask) do
      let fs := factories source 0
      for middleMask in List.range 8 do
        for middle in orders (requests middleMask) do
          if first : ∀ k ∈ middle, k ∈ source then
            for targetMask in List.range 8 do
              for target in orders (requests targetMask) do
                if second : ∀ k ∈ target, k ∈ middle then
                  for c in [0,7,23] do
                    let data := build fs c
                    let twice := projectResults (projectResults data middle first) target second
                    let direct := projectResults data target (fun k h => first k (second k h))
                    let splitFactories := project (project fs middle first) target second
                    let directFactories := project fs target (fun k h => first k (second k h))
                    let expected := oracle source target c
                    unless flatten twice == expected && flatten direct == expected &&
                        flatten (build splitFactories c) == expected &&
                        flatten (build directFactories c) == expected do
                      throw (IO.userError "composed view differs from independent first-occurrence oracle")
                    cases := cases+1
  unless cases == 5184 do throw (IO.userError "composition coverage drift")
  IO.println s!"FUNCTIONAL-VIEW-COMPOSITION-OK cases={cases} contexts=3 orderings=3 inconsistentDuplicates=true"
#eval run

private def lookupChecks : List Nat → Nat → Nat
  | [], _ => 0
  | head :: tail, key => if head == key then 1 else 1 + lookupChecks tail key
private def projectionChecks (source target : List Nat) : Nat :=
  (target.map (lookupChecks source)).foldl Nat.add 0
#eval do
  let saving := projectionChecks [0,1,2] [2,1,0] + projectionChecks [2,1,0] [0]
  let direct := projectionChecks [0,1,2] [0]
  let repeated := List.replicate 10 2
  let retained := projectionChecks [0,1,2] [2] + projectionChecks [2] repeated
  let rescan := projectionChecks [0,1,2] repeated
  unless saving == 9 && direct == 1 && retained == 13 && rescan == 30 do
    throw (IO.userError "projection comparison control drift")
  IO.println "FUNCTIONAL-VIEW-COMPOSITION-COST-OK positive=9/1 negative=13/30 structuralOnly=true"

-- Same-key projection is a normalization, not an identity, for arbitrary tuples.
example : projectResults (Value := Value) (context := 0) (source := [0,0])
    ((11 : Nat),(99 : Nat),PUnit.unit) [0,0] (fun _ h => h) ≠ ((11 : Nat),(99 : Nat),PUnit.unit) := by
  intro same
  have conflict := congrArg (fun data : Results Value 0 [0,0] => data.2.1) same
  change (11 : Nat) = 99 at conflict
  omega

-- Arbitrary dependent families are covered by the public law, without Nat coercions.
example {C K : Type} [DecidableEq K] {V : C → K → Type} {c : C} {source : List K}
    (data : Results V c source) (middle final : List K)
    (first : ∀ k ∈ middle, k ∈ source) (second : ∀ k ∈ final, k ∈ middle) :
    projectResults (projectResults data middle first) final second =
      projectResults data final (fun k h => first k (second k h)) :=
  projectResults_trans data middle final first second

#print axioms resultAt_project
#print axioms projectResults_trans
#print axioms factoryAt_project
#print axioms project_trans
end LeanPoo.Tests.FunctionalViewComposition
