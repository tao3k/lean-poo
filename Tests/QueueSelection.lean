import LeanPoo.Functional.QueueSelection
import LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Tests.QueueSelection
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  for n in [0,1,8,32,128,1024] do
    for family in ["diamond","dense","ring","skewed","gated","quorum","hubchain","bursts"] do
      -- Both seeds have the same exact read topology. Compile and prepare once;
      -- the existing reconfiguration protocol retains the expression/index data.
      let base := compile (ClosureScenarios.equations family n 16 false)
      have source : base.source = ClosureScenarios.equations family n 16 false := compile_source _
      let edges := base.edgeCount
      let referencePreparation := QueueSelection.prepare QueueSelection.reference base
      let otherProfiles : List QueueSelection.Profile := [⟨⟨0,0,0⟩,0⟩,⟨⟨1,4,4⟩,0⟩,⟨⟨1,4,4⟩,1000⟩]
      let preparations : List (Σ profile, QueueSelection.Prepared profile base) :=
        ⟨QueueSelection.reference,referencePreparation⟩ ::
          otherProfiles.map (fun profile => ⟨profile,QueueSelection.prepare profile base⟩)
      for seed in [false,true] do
        let equations := ClosureScenarios.reseed family n 16 base seed
        have same : ∀ index, dependencies (equations index) = dependencies (base.source index) :=
          ClosureScenarios.reseed_dependencies family n 16 base false seed source
        let plan := reconfigure base equations same
        -- These are exact fresh-compiler semantics, not merely equal solutions.
        have fresh : plan = compile (ClosureScenarios.equations family n 16 seed) := by
          exact (QueueSelection.reconfigure_compile _ equations same).trans
            (congrArg compile (ClosureScenarios.reseed_eq family n 16 base false seed source))
        have edgeCount : plan.edgeCount = edges := rfl
        -- Profiles often select the same pure solver. Standard thunks preserve
        -- every check while avoiding repeated execution of that identical solver.
        let appended := Thunk.mk (fun _ => fastClose plan)
        let chunked := Thunk.mk (fun _ => ChunkedClosure.close plan)
        let old := appended.get
        for entry in preparations do
          let prepared := entry.2.reconfigure equations same
          let result := prepared.runCached appended chunked rfl rfl
          have actual : result = prepared.run :=
            QueueSelection.Prepared.runCached_eq prepared appended chunked rfl rfl
          -- chargeRun_eq preserves the same two ceiling checks while sharing
          -- this actual run. Reading charge twice used to execute more solvers.
          let charge := prepared.chargeRun result
          unless result.store == old.store &&
              (result.stats.pops,result.stats.evaluations,result.stats.nodes,result.stats.writes,result.stats.pushes) ==
              (old.stats.pops,old.stats.evaluations,old.stats.nodes,old.stats.writes,old.stats.pushes) do
            throw (IO.userError "selected exact core")
          unless charge ≤ prepared.appendCeiling && charge ≤ prepared.hybridCeiling &&
              result.work.copied+result.work.frames ≤ edges do throw (IO.userError "selected cost")
          for index in List.finRange n do
            unless result.store[index.val] == ClosureScenarios.oracle family seed index.val do throw (IO.userError "scalar oracle")
        let prepared := referencePreparation.reconfigure equations same
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
#print axioms QueueSelection.Prepared.chargeRun_eq
#print axioms QueueSelection.small_degrees_append
#print axioms QueueSelection.canonical
#print axioms QueueSelection.requested_words
#print axioms QueueSelection.selected_with_setup
#print axioms QueueSelection.reconfigure_choice
#print axioms QueueSelection.prepare_reconfigure
#print axioms QueueSelection.reconfigure_compile
#print axioms QueueSelection.Prepared.runCached_eq
#print axioms ClosureScenarios.reseed_eq
#print axioms ClosureScenarios.reseed_dependencies
end LeanPoo.Tests.QueueSelection
