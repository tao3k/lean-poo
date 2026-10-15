import LeanPoo.Functional.HybridClosure
import LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Tests.HybridClosure
open Functional PositiveEquations IncrementalClosure

def scenario (family : String) (n : Nat) (seed : Bool) : Except String Unit := do
  let plan := compile (ClosureScenarios.equations family n 16 seed)
  let old := fastClose plan
  for prices in ([⟨0,0,0⟩,⟨1,4,4⟩,⟨9,0,0⟩,⟨2,1,1⟩] : List Functional.HybridClosure.Prices) do
    let result := Functional.HybridClosure.measured prices plan
    unless result.store.toArray == old.store.toArray &&
      (result.stats.pops,result.stats.evaluations,result.stats.nodes,result.stats.writes,result.stats.pushes) ==
      (old.stats.pops,old.stats.evaluations,old.stats.nodes,old.stats.writes,old.stats.pushes) do throw "core refinement"
    for index in List.finRange n do
      unless result.store[index.val] == ClosureScenarios.oracle family seed index.val do throw "independent scalar oracle"
    let fee := result.work.fee prices
    unless fee ≤ prices.copy*result.stats.pushes && fee ≤ (prices.suspend+prices.resume)*result.stats.writes &&
      result.work.copied+result.work.frames ≤ result.stats.pushes && result.work.frames ≤ n do
      throw "differential fee or allocation bound"
  -- A chain has only empty/singleton outgoing lists: no suspension is needed.
  if family == "ring" && seed then
    let result := Functional.HybridClosure.measured Functional.HybridClosure.balanced plan
    unless result.work.frames == 0 do throw "singleton inline fast path"

#eval show IO Unit from do
  for n in [0,1,8,32,128] do
    for family in ["diamond","dense","ring","skewed","gated","quorum","hubchain","bursts"] do
      for seed in [false,true] do IO.ofExcept (scenario family n seed)
  IO.println "HYBRID-CLOSURE-OK scenarios=80 profiles=4 exact-core scalar-oracle local-price-bound append-allocation-bound singleton-fastpath"
#print axioms Functional.HybridClosure.execute_refines
#print axioms Functional.HybridClosure.measured_bounds
#print axioms Functional.HybridClosure.fee_bound
#print axioms Functional.HybridClosure.balanced_allocation
#print axioms Functional.HybridClosure.frame_bound
#print axioms Functional.HybridClosure.balanced_words
end LeanPoo.Tests.HybridClosure
