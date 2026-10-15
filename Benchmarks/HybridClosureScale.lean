import LeanPoo.Functional.HybridClosure
import LeanPoo.Functional.ClosureScenarios
open LeanPoo.Functional PositiveEquations IncrementalClosure

namespace HybridClosureScale

def main (args : List String) : IO Unit := do
  let [queue,family,size,width,seeded,scope] := args | throw (IO.userError "queue family n width seed scope")
  let some n := size.toNat? | throw (IO.userError "n")
  let some width := width.toNat? | throw (IO.userError "width")
  unless ["append","chunked","hybrid"].contains queue && n > 0 && width > 0 &&
    ["diamond","dense","ring","skewed","gated","quorum","hubchain","bursts"].contains family &&
    ["true","false"].contains seeded && ["cold","warm"].contains scope do throw (IO.userError "parameters")
  let seed := seeded == "true"
  let sources ← IO.mkRef (ClosureScenarios.equations family n width seed)
  let warm ← if scope == "warm" then
      IO.mkRef (some (compile (← sources.get))) else IO.mkRef (none : Option (Plan n))
  let last ← IO.mkRef ((Vector.replicate n false),({} : Stats),({} : HybridClosure.Work),(0 : Nat))
  let repetitions := if scope == "cold" then 5 else 400
  let begin ← IO.monoNanosNow
  for _ in List.range repetitions do
    let source ← sources.get
    let retained ← warm.get
    let plan := match retained with | some plan => plan | none => compile source
    let (facts,stats,work) := if queue == "hybrid" then
        let run := HybridClosure.measured HybridClosure.balanced plan
        (run.store,run.stats,run.work)
      else if queue == "append" then
        let run := fastClose plan
        (run.store,run.stats,({copied := run.stats.pushes} : HybridClosure.Work))
      else
        let run := ChunkedClosure.close plan
        (run.store,run.stats,({frames := run.stats.writes} : HybridClosure.Work))
    last.set (facts,stats,work,plan.edgeCount)
  let elapsed := (← IO.monoNanosNow)-begin
  let (facts,stats,work,edges) ← last.get
  for index in List.finRange n do
    unless facts[index.val] == ClosureScenarios.oracle family seed index.val do throw (IO.userError "scalar oracle")
  let fee := work.fee HybridClosure.balanced
  unless stats.pops ≤ n+edges && stats.writes ≤ n do throw (IO.userError "core bound")
  if queue == "hybrid" then
    unless fee ≤ stats.pushes && fee ≤ 8*stats.writes && work.copied+work.frames ≤ stats.pushes && work.frames ≤ n do
      throw (IO.userError "local scheduling bound")
  IO.println s!"queue={queue} family={family} n={n} width={width} seed={seed} scope={scope} repetitions={repetitions} query_ns={elapsed} pops={stats.pops} evals={stats.evaluations} nodes={stats.nodes} writes={stats.writes} pushes={stats.pushes} edges={edges} copied_queue={work.copied} frame_allocations={work.frames} queue_pairs={n+work.copied+work.frames} empty_schedules={work.empty} shared_schedules={work.shared} inline_schedules={work.inlined} selected_fee={fee} oracle_parity=true"
end HybridClosureScale

def main := HybridClosureScale.main
