import LeanPoo.Functional.ClosureScenarios
import LeanPoo.Functional.ClosurePolicy

namespace LeanPoo.Tests.ClosureCosts
open Functional PositiveEquations IncrementalClosure

def scenario (family : String) (n : Nat) (seed : Bool) : Except String Unit := do
  let source := ClosureScenarios.equations family n 16 seed
  let plan := compile source
  let actual := ChunkedClosure.close plan
  let original := fastClose plan
  unless actual.store.toArray == original.store.toArray && (actual.stats.pops,actual.stats.evaluations,actual.stats.nodes,actual.stats.writes,actual.stats.pushes) ==
      (original.stats.pops,original.stats.evaluations,original.stats.nodes,original.stats.writes,original.stats.pushes) do
    throw "chunk representation refinement"
  for index in List.finRange n do
    unless actual.store[index.val] == ClosureScenarios.oracle family seed index.val do throw "scalar oracle"
  let sampleLayout : Functional.ClosureCosts.Layout := ⟨8,by decide,1,1,2,4,20⟩
  let price : Functional.ClosureCosts.Prices := ⟨2,3,5,7⟩
  let selected := ClosurePolicy.choose plan price sampleLayout
  for candidate in [ClosurePolicy.Queue.append,.chunked] do
    unless ClosurePolicy.upper plan price sampleLayout selected ≤ ClosurePolicy.upper plan price sampleLayout candidate &&
      ClosurePolicy.queueCeiling plan (ClosurePolicy.minimumAllocation plan) ≤ ClosurePolicy.queueCeiling plan candidate do
      throw "minimum declared ceiling"
  let bytes := Functional.ClosureCosts.encode actual.store
  unless (Functional.ClosureCosts.decode bytes).toArray == actual.store.toArray do throw "byte roundtrip"
  for index in List.finRange n do
    unless Functional.ClosureCosts.write bytes index == Functional.ClosureCosts.encode (actual.store.set index.val true index.isLt) do
      throw "byte write refinement"
  for owned in [false,true] do
    for chunked in [false,true] do
      for scalar in [false,true] do
        for snapshot in [false,true] do
          let representation : Functional.ClosureCosts.Representation := ⟨owned,chunked,scalar,snapshot⟩
          for layout in ([⟨4,by decide,1,1,2,4,20⟩,⟨8,by decide,1,1,2,4,20⟩] : List Functional.ClosureCosts.Layout) do
            let price : Functional.ClosureCosts.Prices := ⟨2,3,5,7⟩
            unless Functional.ClosureCosts.solveWords layout representation n actual.stats ≤
              Functional.ClosureCosts.solveWords layout representation n (Functional.ClosureCosts.ceiling plan) &&
              Functional.ClosureCosts.charge price layout representation n actual.stats ≤
              Functional.ClosureCosts.charge price layout representation n (Functional.ClosureCosts.ceiling plan) do
              throw "allocation or primitive bound"
  if n ≤ 32 then
    unless ChunkedClosure.frameAllocations (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ == actual.stats.writes &&
      ChunkedClosure.peakFrames (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ ≤ n do
      throw "operational frame allocation or peak"

#eval show IO Unit from do
  for n in [0,1,8,32,128] do
    for family in ["diamond","dense","ring","skewed","gated","quorum"] do
      for seed in [false,true] do IO.ofExcept (scenario family n seed)
  IO.println "CLOSURE-COSTS-OK cases=60 representation-policies=16 word-widths=2 scalar-oracle byte-writes frame-allocation peak bound"
#print axioms Functional.ClosureCosts.decode_encode
#print axioms Functional.ClosureCosts.backend_bound
#print axioms Functional.ChunkedClosure.execute_refines
#print axioms Functional.ChunkedClosure.frame_allocation_bound
#print axioms Functional.ChunkedClosure.peak_frame_bound
end LeanPoo.Tests.ClosureCosts
