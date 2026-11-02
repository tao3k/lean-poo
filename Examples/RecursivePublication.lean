import Examples.Support.RecursiveTopology
import LeanPoo.Functional.RecursivePublication

/-! Three entry points share eight actual graph revisions. Each entry's context
is distinct; graph closure, current refinement and exact evidence are composed
without treating late effect refusal as a graph rollback. Sequential future work. -/
namespace LeanPoo.Examples.RecursivePublication
open Functional
abbrev Entry := Fin 3
abbrev Context := Entry × Nat
abbrev Snapshot := RecursiveTopologies.Snapshot
abbrev World := Functional.RecursivePublication.World Snapshot Entry Context
abbrev Request := RecursiveStaging.Request Snapshot Nat String
abbrev Evidence := (RecursiveTopologies.Node × Nat) × Nat × Context

/-- The existing independent invocation template specialized to distinct contexts. -/
def Call : DeclarativeMetadata.Contract Unit (RecursiveTopologies.Node × Nat) Evidence where
  input := ⟨"reference",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"evidence",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Refine current computed dependencies before the per-entry invocation gate. -/
def refineCurrent (snapshot : Snapshot) : Except String Unit := do
  unless (ObjectContract.diagnose
      (RecursiveTopologies.schema (RecursiveTopologies.reportTotal snapshot.source)) snapshot []).isEmpty do
    throw "refine"

/-- Exact evidence refuses cross-entry context transplantation. Successful effects
increment only their own context; construction of the graph is not repeated. -/
def effect (entry : Entry) (foreign : Option Context := none)
    (snapshot : Snapshot) (context : Context) : Except String (Evidence × Context) := do
  refineCurrent snapshot
  let root := snapshot.graph.canonical 11
  let bound := Call.bindEvidence root 7 context (fun value => value)
  match bound.publish context
      (fun _ => (.ok ((root,7,foreign.getD context),(entry,context.2+1)) : Except String (Evidence × Context))) root with
  | (.ok result,next) => return (result,next)
  | (.error _,_) => throw "logic"

/-- Isolate refusal after current graph refinement, leaving its entry context intact. -/
def refusing (snapshot : Snapshot) (_context : Context) : Except String (Evidence × Context) := do
  refineCurrent snapshot
  throw "policy"

/-- Explicit preparation captures the one shared observed head for any entry. -/
def prepare (world : World) (source : RecursiveTopologies.Source) : Except String Request :=
  RecursiveRestaging.restage world.graph 0 (fun _ => .ok (fun old => RecursiveTopologies.step old source))

/-- A stale request keeps the current shared head regardless of originating entry. -/
def stale (request : Request) (world : World) : Bool :=
  match RecursiveStaging.publish request world.graph 0 with
  | (.error .stale,kept) => kept.revision == world.graph.revision &&
      kept.value.graph.canonical 11 == world.graph.value.graph.canonical 11
  | _ => false

/-- Prepare multiple entries before replaying history, refuse closure, re-stage,
install despite a late policy failure, reject foreign evidence and retry the effect. -/
def round (state : World × List Request) (stage : Nat) : Except String (World × List Request) := do
  let (world,history) := state
  let entry : Entry := ⟨world.graph.revision % 3,by omega⟩
  let other : Entry := ⟨(entry.val+1)%3,by omega⟩
  let source : RecursiveTopologies.Source := ⟨stage,false⟩
  let pending ← prepare world source
  let sibling ← prepare world source
  let failed ← prepare world ⟨stage,true⟩
  unless history.all (fun old => stale old world) do throw "old work before restaging"
  match Functional.RecursivePublication.submit failed world 0 entry (effect entry) with
  | (.error (.rejected "joint refusal"),kept) =>
    unless kept.graph.revision == world.graph.revision &&
        kept.graph.value.graph.canonical 11 == world.graph.value.graph.canonical 11 do throw "closure refusal state"
  | _ => throw "closure failure phase"
  let retry ← prepare world source
  let installed ← match Functional.RecursivePublication.submit retry world 0 entry refusing with
    | (.ok (.error "policy"),next) => pure next
    | _ => throw "late policy refusal"
  unless (installed.graph.value.graph.payload 11).total == RecursiveTopologies.reportTotal source &&
      installed.contexts entry == world.contexts entry do throw "lost installed head or changed context"
  unless (pending :: sibling :: history).all (fun old => stale old installed) do throw "entry sibling revived"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source) installed.graph.value.epochs 11
      (world.graph.value.graph.canonical 11)) do throw "old report revived"
  unless installed.graph.value.graph.canonical 12 == world.graph.value.graph.canonical 12 do throw "idle rebuilt"
  match Functional.RecursivePublication.observe installed other (effect other (some (world.contexts entry))) with
  | (.error "logic",kept) => unless kept.contexts other == world.contexts other do throw "foreign context changed"
  | _ => throw "foreign context accepted"
  match Functional.RecursivePublication.observe installed entry (effect entry) with
  | (.ok _,next) =>
    unless next.graph.revision == installed.graph.revision &&
        next.contexts entry == (entry,(world.contexts entry).2+1) &&
        next.contexts other == world.contexts other do throw "effect-only retry state"
    return (next,pending :: sibling :: history)
  | _ => throw "effect-only retry refused"

/-- Matching Gerbil catalogs and per-entry commit counts across restored membership. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let initial : World := ⟨⟨0,first⟩,fun entry => (entry,0)⟩
  let (last,_) ← [1,2,3,0,1,2,5,6].foldlM round (initial,[])
  unless last.graph.revision == 8 && (last.graph.value.graph.payload 11).total == 135 &&
      ((List.finRange 3).map (fun entry => (last.contexts entry).2)) == [3,3,2] do throw "final state"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names last.graph.value.source)
      last.graph.value.epochs 8 (first.graph.canonical 8)) do throw "old provider revived"

#print axioms Functional.RecursivePublication.observe_graph
#print axioms Functional.RecursivePublication.observe_refused
#print axioms Functional.RecursivePublication.observe_other
#print axioms Functional.RecursivePublication.graph_refused
#print axioms Functional.RecursivePublication.late_refusal
#print axioms Functional.RecursivePublication.installed_graph
#print axioms Functional.RecursivePublication.submit_other
#print axioms Functional.RecursivePublication.sibling_stale
#eval match test with
  | .ok () => IO.println "RECURSIVE-PUBLICATION-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursivePublication
