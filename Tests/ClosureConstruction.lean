import LeanPoo.Functional.ClosureConstruction
import LeanPoo.Functional.ClosureScenarios

namespace LeanPoo.Tests.ClosureConstruction
open Functional PositiveEquations IncrementalClosure
#eval show IO Unit from do
  for n in [0,1,32,256] do
    for family in ["diamond","dense","ring","bursts","hubchain","quorum","skewed"] do
      for seed in [false,true] do
        let source := ClosureScenarios.equations family n 16 seed
        let fused := ClosureConstruction.compile source
        let previous := IncrementalClosure.compile source
        unless fused.watches == previous.watches do throw (IO.userError "fused exact index")
        let result := (ClosureLifecycle.prepare .cold fused).run
        let reference := fastClose previous
        unless result.store == reference.store && result.stats == reference.stats do
          throw (IO.userError "fused exact core")
        for index in List.finRange n do
          unless result.store[index.val] == ClosureScenarios.oracle family seed index.val do
            throw (IO.userError "independent source oracle")
  IO.println "CLOSURE-CONSTRUCTION-OK exact-index exact-core scalar-oracle"
#print axioms ClosureConstruction.copyIndexed_spec
#print axioms ClosureConstruction.fusedIndex_eq
#print axioms ClosureConstruction.reshape_canonical
#print axioms ClosureConstruction.fusion_saving
#print axioms ClosureConstruction.visitor_saving
#print axioms ClosureConstruction.preparation_paid
#print axioms ClosureConstruction.ensureAdaptive_idempotent
end LeanPoo.Tests.ClosureConstruction
