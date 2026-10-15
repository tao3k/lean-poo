import LeanPoo.Functional.ClosureLifecycle
import LeanPoo.Functional.ClosureScenarios
import Lean.Data.Json
open LeanPoo.Functional PositiveEquations IncrementalClosure Lean
namespace HybridClosureScale

structure Built (family : String) (n width : Nat) where
  seed : Bool
  plan : Plan n
  source : plan.source = ClosureScenarios.equations family n width seed
  cached : ClosureLifecycle.Prepared plan

def build (mode : ClosureLifecycle.Mode) (family : String) (n width : Nat) (seed : Bool) : Built family n width :=
  let plan := compile (ClosureScenarios.equations family n width seed)
  ⟨seed,plan,compile_source _,ClosureLifecycle.prepare mode plan⟩

def refresh (old : Built family n width) (seed : Bool) : Built family n width :=
  let source := ClosureScenarios.equations family n width seed
  let same : ∀ index, dependencies (source index) = dependencies (old.plan.source index) := by
    intro index
    rw [old.source]
    exact ClosureScenarios.dependencies_seed family n width _ _ index
  ⟨seed,reconfigure old.plan source same,reconfigure_source _ _ _,old.cached.reconfigure source same⟩

def label : ClosureLifecycle.Mode → String
  | .cold => "cold" | .adaptive => "auto" | .append => "append" | .chunked => "chunked" | .hybrid => "hybrid"
def engineLabel : QueueSelection.Queue → String
  | .append => "append" | .chunked => "chunked" | .hybrid => "hybrid"

def main (args : List String) : IO Unit := do
  let [queue,family,size,widthText,seedText,scope] := args | throw (IO.userError "queue family n width seed scope")
  let some n := size.toNat? | throw (IO.userError "n")
  let some width := widthText.toNat? | throw (IO.userError "width")
  unless ["append","chunked","hybrid","auto"].contains queue && n > 0 && width > 0 &&
    ["diamond","dense","ring","skewed","gated","quorum","hubchain","bursts"].contains family &&
    ["true","false"].contains seedText && ["cold","warm","refresh"].contains scope do throw (IO.userError "parameters")
  let seed := seedText == "true"
  let mode : ClosureLifecycle.Mode := match queue with
    | "append" => .append | "chunked" => .chunked | "hybrid" => .hybrid
    | _ => if scope == "cold" then .cold else .adaptive
  let setupStart ← IO.monoNanosNow
  let prior ← IO.mkRef (if scope == "cold" then none else some (build mode family n width (if scope == "refresh" then !seed else seed)))
  let setupElapsed := (← IO.monoNanosNow)-setupStart
  let setupNanos := if scope == "cold" then 0 else setupElapsed
  let setupVisits := match ← prior.get with | none => 0 | some prior => prior.cached.visits
  let last ← IO.mkRef (none : Option (Built family n width × HybridClosure.Run n))
  let repetitions := if scope == "warm" then 400 else 5
  let begin ← IO.monoNanosNow
  for _ in List.range repetitions do
    let retained ← prior.get
    let compiled := match retained with
      | none => build mode family n width seed
      | some old => if scope == "refresh" then refresh old seed else old
    let result := compiled.cached.run
    last.set (some (compiled,result))
  let elapsed := (← IO.monoNanosNow)-begin
  let some (built,result) ← last.get | throw (IO.userError "missing execution")
  let stats := result.stats
  let work := result.work
  let prepared := built.cached
  let engine := engineLabel prepared.choose
  for index in List.finRange n do
    unless result.store[index.val] == ClosureScenarios.oracle family seed index.val do throw (IO.userError "scalar oracle")
  let charge := work.fee QueueSelection.reference.prices+(if engine == "hybrid" then stats.writes else 0)
  unless stats.pops ≤ n+prepared.edges && stats.writes ≤ n do throw (IO.userError "core bound")
  if queue == "auto" then
    unless charge ≤ prepared.ceiling .append && charge ≤ prepared.ceiling .chunked && charge ≤ prepared.ceiling .hybrid do
      throw (IO.userError "selected ceiling")
  let astNodes := (List.ofFn (fun index : Fin n => nodes built.plan.equations[index.val])).sum
  let fields : List (String × Json) := [
    ("queue",toJson queue),("engine",toJson engine),("family",toJson family),("n",toJson n),("width",toJson width),
    ("seed",toJson seedText),("scope",toJson scope),("repetitions",toJson repetitions),("query_ns",toJson elapsed),
    ("setup_ns",toJson setupNanos),("lifecycle_ns",toJson (elapsed+setupNanos)),("cache_mode",toJson (label mode)),
    ("construction_nodes",toJson astNodes),("index_links",toJson (if scope == "cold" then prepared.edges else 0)),
    ("selector_visits",toJson (if scope == "warm" then 0 else prepared.visits)),("setup_selector_visits",toJson setupVisits),
    ("pops",toJson stats.pops),("evals",toJson stats.evaluations),("nodes",toJson stats.nodes),
    ("writes",toJson stats.writes),("pushes",toJson stats.pushes),("edges",toJson prepared.edges),
    ("copied_queue",toJson work.copied),("frame_allocations",toJson work.frames),("queue_pairs",toJson (n+work.copied+work.frames)),
    ("empty_schedules",toJson work.empty),("shared_schedules",toJson work.shared),("inline_schedules",toJson work.inlined),
    ("selected_fee",toJson (work.fee HybridClosure.balanced)),("policy_charge",toJson charge),
    ("append_ceiling",toJson (prepared.ceiling .append)),("chunk_ceiling",toJson (prepared.ceiling .chunked)),
    ("hybrid_ceiling",toJson (prepared.ceiling .hybrid)),("oracle_parity",toJson true)]
  IO.println (Json.mkObj fields).compress
end HybridClosureScale

def main := HybridClosureScale.main
