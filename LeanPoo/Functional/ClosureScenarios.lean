import LeanPoo.Functional.ClosureCosts

/-! Shared finite workloads for representation/cost controls. Independent scalar
oracles are declared separately from the equation interpreter. -/
namespace LeanPoo.Functional.ClosureScenarios
open PositiveEquations

def equations (family : String) (n width : Nat) (seed : Bool) : Equations n := fun index =>
  if zero : index.val = 0 then
    if family == "ring" then .either (.literal seed) (.read ⟨n-1,by have := index.isLt; omega⟩)
    else .literal seed
  else if family == "dense" then
    (List.finRange index.val).foldl (fun expression earlier =>
      .either expression (.read ⟨earlier.val,Nat.lt_trans earlier.isLt index.isLt⟩)) (.literal false)
  else if family == "diamond" then
    if join : index.val % 3 = 0 then
      .both (.read ⟨index.val-1,by omega⟩) (.read ⟨index.val-2,by omega⟩)
    else .read ⟨index.val-index.val%3,by have : 0 < index.val % 3 := Nat.pos_of_ne_zero join; omega⟩
  else if family == "hubchain" then
    if index.val % 16 == 0 then .either (.read ⟨0,by omega⟩) (.read ⟨index.val-1,by omega⟩)
    else .read ⟨index.val-1,by omega⟩
  else if family == "bursts" then
    if hub : index.val % 32 = 0 then .read ⟨index.val-1,by omega⟩
    else .read ⟨index.val-index.val%32,by have positive := Nat.pos_of_ne_zero hub; omega⟩
  else if family == "skewed" then
    (List.range width).foldl (fun expression _ => .either expression (.read ⟨index.val-1,by omega⟩)) (.literal false)
  else if family == "gated" then .both (.read ⟨0,by omega⟩) (.literal (index.val%2 == 0))
  else if family == "quorum" then
    Expr.twoOfThree (.read ⟨index.val-1,by omega⟩) (.read ⟨index.val-1,by omega⟩) (.read ⟨0,by omega⟩)
  else .read ⟨index.val-1,by omega⟩

def oracle (family : String) (seed : Bool) (index : Nat) := seed && (family != "gated" || index%2 == 0)
end LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Functional.ClosureScenarios
open PositiveEquations IncrementalClosure
theorem dependencies_seed (family : String) (n width : Nat) (left right : Bool) (index : Fin n) :
    dependencies (equations family n width left index) = dependencies (equations family n width right index) := by
  unfold equations
  split
  · split <;> rfl
  · rfl

/-- Only the root equation observes the seed; other expression trees can be shared. -/
theorem equations_nonzero (family : String) (n width : Nat) (left right : Bool)
    (index : Fin n) (nonzero : index.val ≠ 0) :
    equations family n width left index = equations family n width right index := by
  simp [equations, nonzero]

/-- Revise the root literal while retaining every other compiled expression. -/
def reseed (family : String) (n width : Nat) (base : Plan n) (seed : Bool) : Equations n :=
  fun index => if index.val = 0 then equations family n width seed index else base.source index

/-- A source certificate makes shared-expression revision equal to fresh construction. -/
theorem reseed_eq (family : String) (n width : Nat) (base : Plan n) (before after : Bool)
    (source : base.source = equations family n width before) :
    reseed family n width base after = equations family n width after := by
  funext index
  simp only [reseed]
  split
  · rfl
  · rename_i nonzero
    rw [source]
    exact equations_nonzero family n width before after index nonzero

/-- Literal revision retains the exact read topology needed by reconfigure. -/
theorem reseed_dependencies (family : String) (n width : Nat) (base : Plan n) (before after : Bool)
    (source : base.source = equations family n width before) (index : Fin n) :
    dependencies (reseed family n width base after index) = dependencies (base.source index) := by
  rw [reseed_eq family n width base before after source, source]
  exact dependencies_seed family n width after before index
end LeanPoo.Functional.ClosureScenarios
