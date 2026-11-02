import LeanPoo.Functional.IncrementalClosure

/-! Independent scalar controls and explicit-cost bounds for the actual tail
runtime, including duplicate edges, least-cycle revocation and index retention. -/
namespace LeanPoo.Tests.IncrementalClosure
open Functional Functional.PositiveEquations Functional.IncrementalClosure

def replaceConstants (value : Bool) : Expr n → Expr n
  | .literal _ => .literal value
  | .read index => .read index
  | .both left right => .both (replaceConstants value left) (replaceConstants value right)
  | .either left right => .either (replaceConstants value left) (replaceConstants value right)

theorem replace_dependencies (value : Bool) (expression : Expr n) :
    dependencies (replaceConstants value expression) = dependencies expression := by
  induction expression <;> simp_all [replaceConstants,dependencies]

def graph (n : Nat) (shared ring reverse : Bool) : Equations n := fun index =>
  if reverse then
    if last : index.val+1 = n then .literal true else .read ⟨index.val+1,by omega⟩
  else if zero : index.val = 0 then
    if ring then .either (.literal true) (.read ⟨n-1,by have := index.isLt; omega⟩) else .literal true
  else
    let previous : Fin n := ⟨index.val-1,by omega⟩
    if shared then .both (.read previous) (.read previous) else .read previous

def scenario (n : Nat) (shared ring reverse : Bool) : Except String Unit := do
  let source := graph n shared ring reverse
  let plan := compile source
  let result := fastClose plan
  let edgeCount := plan.edgeCount
  unless result.store.toArray.all id && result.stats.pops ≤ n+edgeCount && result.stats.writes ≤ n &&
      result.stats.evaluations ≤ result.stats.pops && result.stats.nodes ≤ result.stats.evaluations*plan.maxNodes &&
      edgeCount == (edges source).length do throw "oracle or certified primitive bound"
  if !reverse && !ring then
    let multiplicity := if shared then 2 else 1
    unless result.stats.evaluations == n && result.stats.writes == n &&
        result.stats.pushes == multiplicity*(n-1) && result.stats.pops == n+multiplicity*(n-1) &&
        result.stats.nodes == (if n == 0 then 0 else 1+(if shared then 3 else 1)*(n-1)) do
      throw "linear chain exact operations"
  let next : Equations n := fun index => replaceConstants false (source index)
  let retained := reconfigure plan next (by intro index; rw [compile_source]; exact replace_dependencies _ _)
  let revoked := fastClose retained
  unless !(revoked.store.toArray.any id) && retained.watches.toArray == plan.watches.toArray do
    throw "least revocation or retained topology"
  -- Small cases compare against the original fully certified reference path.
  if n ≤ 8 then
    unless result.store.toArray == (Vector.ofFn (PositiveEquations.close source).value).toArray do
      throw "reference semantics"

#eval show IO Unit from do
  for n in [0,1,2,4,8,16,64,256,1024] do
    for shared in [false,true] do
      for ring in [false,true] do
        for reverse in [false,true] do IO.ofExcept (scenario n shared ring reverse)
  IO.println "INCREMENTAL-CLOSURE-OK cases=72 scalar-oracle primitive-bounds exact-linear-counts retained-index cyclic-revocation"
#print axioms IncrementalClosure.fast_canonical
#print axioms IncrementalClosure.fast_pop_bound
#print axioms IncrementalClosure.compiled_edge_count
end LeanPoo.Tests.IncrementalClosure
