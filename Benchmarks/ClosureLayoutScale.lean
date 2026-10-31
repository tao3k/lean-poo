import LeanPoo.Functional.ClosureScenarios
open LeanPoo.Functional
open PositiveEquations IncrementalClosure

namespace ClosureLayoutScale

def main (args : List String) : IO Unit := do
  let [variant,family,size,width,seeded] := args | throw (IO.userError "variant family n width seed")
  let some n := size.toNat? | throw (IO.userError "n")
  let some width := width.toNat? | throw (IO.userError "width")
  unless ["append","chunked"].contains variant && n > 0 && width > 0 &&
    ["diamond","dense","ring","skewed","gated","quorum"].contains family && ["true","false"].contains seeded do
    throw (IO.userError "parameters")
  let seed := seeded == "true"
  let begin ← IO.monoNanosNow
  let plan := compile (ClosureScenarios.equations family n width seed)
  let (facts,stats) ← if variant == "append" then
      let result := fastClose plan
      (← IO.mkRef (result.store,result.stats)).get
    else
      let result := ChunkedClosure.close plan
      (← IO.mkRef (result.store,result.stats)).get
  let elapsed := (← IO.monoNanosNow)-begin
  for index in List.finRange n do
    unless facts[index.val] == ClosureScenarios.oracle family seed index.val do throw (IO.userError "scalar oracle")
  let representation : ClosureCosts.Representation := ⟨true,variant=="chunked",true,true⟩
  let layout : ClosureCosts.Layout := ⟨8,by decide,1,1,2,4,20⟩
  let words := ClosureCosts.solveWords layout representation n stats
  let upper := ClosureCosts.solveWords layout representation n (ClosureCosts.ceiling plan)
  unless words ≤ upper && stats.pops ≤ n+plan.edgeCount && stats.writes ≤ n do throw (IO.userError "cost ceiling")
  IO.println s!"variant={variant} family={family} n={n} width={width} seed={seed} query_ns={elapsed} pops={stats.pops} evals={stats.evaluations} nodes={stats.nodes} writes={stats.writes} pushes={stats.pushes} edges={plan.edgeCount} queue_pairs={ClosureCosts.queueCells representation n stats} modeled_solve_words={words} modeled_upper_words={upper} oracle_parity=true"
end ClosureLayoutScale

def main := ClosureLayoutScale.main
