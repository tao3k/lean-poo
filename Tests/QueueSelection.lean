import LeanPoo.Functional.QueueSelection
import LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Tests.QueueSelection
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  for n in [0,1,8,32,128,1024] do
    for family in ["diamond","dense","ring","skewed","gated","quorum","hubchain","bursts"] do
      for seed in [false,true] do
        let plan := compile (ClosureScenarios.equations family n 16 seed)
        let old := fastClose plan
        for profile in ([QueueSelection.reference,⟨⟨0,0,0⟩,0⟩,⟨⟨1,4,4⟩,0⟩,⟨⟨1,4,4⟩,1000⟩] : List QueueSelection.Profile) do
          let prepared := QueueSelection.prepare profile plan
          let result := prepared.run
          unless result.store == old.store &&
              (result.stats.pops,result.stats.evaluations,result.stats.nodes,result.stats.writes,result.stats.pushes) ==
              (old.stats.pops,old.stats.evaluations,old.stats.nodes,old.stats.writes,old.stats.pushes) do
            throw (IO.userError "selected exact core")
          unless prepared.charge ≤ prepared.appendCeiling && prepared.charge ≤ prepared.hybridCeiling &&
              result.work.copied+result.work.frames ≤ plan.edgeCount do throw (IO.userError "selected cost")
          for index in List.finRange n do
            unless result.store[index.val] == ClosureScenarios.oracle family seed index.val do throw (IO.userError "scalar oracle")
        let prepared := QueueSelection.prepare QueueSelection.reference plan
        if ["diamond","ring","hubchain"].contains family then
          unless prepared.choose == .append do throw (IO.userError s!"unexpected engine {family}/{n}")
        if family == "bursts" && n ≥ 128 then
          unless prepared.choose == .hybrid do throw (IO.userError "lost shared-burst strategy")
  IO.println "QUEUE-SELECTION-OK scenarios=96 profiles=4 exact-core scalar-oracle both-ceilings narrow-append burst-hybrid"
#print axioms HybridClosure.execute_credit
#print axioms HybridClosure.measured_credit
#print axioms QueueSelection.reference_threshold
#print axioms QueueSelection.reference_capacity
#print axioms IncrementalClosure.appendWatchers_eq
#print axioms QueueSelection.selected_bound
#print axioms QueueSelection.small_degrees_append
#print axioms QueueSelection.canonical
#print axioms QueueSelection.requested_words
#print axioms QueueSelection.selected_with_setup
#print axioms QueueSelection.reconfigure_choice
end LeanPoo.Tests.QueueSelection
