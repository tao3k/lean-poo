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
  else if family == "skewed" then
    (List.range width).foldl (fun expression _ => .either expression (.read ⟨index.val-1,by omega⟩)) (.literal false)
  else if family == "gated" then .both (.read ⟨0,by omega⟩) (.literal (index.val%2 == 0))
  else if family == "quorum" then
    Expr.twoOfThree (.read ⟨index.val-1,by omega⟩) (.read ⟨index.val-1,by omega⟩) (.read ⟨0,by omega⟩)
  else .read ⟨index.val-1,by omega⟩

def oracle (family : String) (seed : Bool) (index : Nat) := seed && (family != "gated" || index%2 == 0)
end LeanPoo.Functional.ClosureScenarios
