import LeanPoo.Functional.ClosureLifecycle
import LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Tests.ClosureLifecycle
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  for n in [0,1,32,256] do
    for family in ["diamond","dense","ring","hubchain","bursts","gated","quorum"] do
      for seed in [false,true] do
        let source := ClosureScenarios.equations family n 16 seed
        let plan := compile source
        let baseline := fastClose plan
        for mode in [ClosureLifecycle.Mode.cold,.adaptive,.append,.chunked,.hybrid] do
          let prepared := ClosureLifecycle.prepare mode plan
          let actual := prepared.run
          unless actual.store == baseline.store &&
              (actual.stats.pops,actual.stats.nodes,actual.stats.writes,actual.stats.pushes) ==
              (baseline.stats.pops,baseline.stats.nodes,baseline.stats.writes,baseline.stats.pushes) do
            throw (IO.userError "lifecycle exact core")
          unless prepared.visits == (if mode == .adaptive then n else 0) do
            throw (IO.userError "preparation visits")
          if mode == .cold || mode == .adaptive then
            for candidate in [QueueSelection.Queue.append,.chunked,.hybrid] do
              unless prepared.charge ≤ prepared.ceiling candidate do throw (IO.userError "candidate ceiling")
          let revised := prepared.reconfigure (ClosureScenarios.equations family n 16 (!seed)) (by
            intro index
            rw [compile_source]
            exact ClosureScenarios.dependencies_seed _ _ _ _ _ _)
          unless revised.visits == 0 && revised.choose == prepared.choose do
            throw (IO.userError "retained selector")
          let revoked := revised.run
          for index in List.finRange n do
            unless actual.store[index.val] == ClosureScenarios.oracle family seed index.val &&
                revoked.store[index.val] == ClosureScenarios.oracle family (!seed) index.val do
              throw (IO.userError "independent revocation oracle")
        let cold := ClosureLifecycle.prepare .cold plan
        unless cold.upgrade.choose == (ClosureLifecycle.prepare .adaptive plan).choose do
          throw (IO.userError "delayed adaptive preparation")
        if family == "dense" && n == 256 then
          unless cold.choose == .chunked && cold.upgrade.choose == .chunked do
            throw (IO.userError "dense fixed chunk candidate")
  IO.println "CLOSURE-LIFECYCLE-OK five-modes exact-core three-ceilings zero-cold-selector retained-revocation"
#print axioms ClosureLifecycle.canonical
#print axioms ClosureLifecycle.actual_bound
#print axioms ClosureLifecycle.choose_minimum
#print axioms ClosureLifecycle.preparation_regret
#print axioms ClosureLifecycle.retained_preparation
end LeanPoo.Tests.ClosureLifecycle
