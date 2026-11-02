import Examples.Support.RecursiveApprovals
import LeanPoo.Functional.RecursiveCompetition

/-! Competing current/future joint revisions, repeated metadata drift and explicit
restaging over actual SCC graphs. Observer exceptions and queue alias controls are
separate Scheme evidence; this model uses pure locally terminating effect results. -/
namespace LeanPoo.Examples.RecursiveCompetition
open Functional LeanPoo.Examples.RecursiveApprovals
abbrev Submission := Functional.RecursiveCompetition.Submission Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence

/-- Keep captured request versions distinct from the versions observed on attempt. -/
def staged (world : World) (source : RecursiveTopologies.Source) (policy : Policy)
    (captured observed : Nat) (entry : Entry) : Submission :=
  ⟨prepare world source policy captured,observed,entry,refusing⟩

/-- Finite executable projections complement the generic exact-world theorems. -/
def sameWorld (left right : World) : Bool :=
  left.graph.revision == right.graph.revision &&
  left.graph.value.metadata.token == right.graph.value.metadata.token &&
  left.graph.value.metadata.budget == right.graph.value.metadata.budget &&
  left.graph.value.graph.graph.canonical 11 == right.graph.value.graph.graph.canonical 11 &&
  (List.finRange 3).all (fun entry => left.contexts entry == right.contexts entry)

/-- Drifted requests do not consume the current snapshot or another pending request. -/
def checkStale (items : List Submission) (world : World) : Except String Unit := do
  let (trace,kept) := Functional.RecursiveCompetition.run items world
  unless trace.length == items.length && sameWorld kept world && trace.all (fun receipt =>
      match receipt.outcome with
      | .error .stale => sameWorld receipt.world world
      | _ => false) do throw "drifted batch changed world"

/-- Two explicit preparations can both be invalidated. A later winner expires a
different future proposal; that same intent is explicitly prepared in the next round. -/
def round (state : World × List Submission)
    (intents : (RecursiveTopologies.Source × Policy) × (RecursiveTopologies.Source × Policy)) :
    Except String (World × List Submission) := do
  let (world,history) := state
  let ((source,policy),(futureSource,futurePolicy)) := intents
  let entry : Entry := ⟨world.graph.revision%3,by omega⟩
  let other : Entry := ⟨(entry.val+1)%3,by omega⟩
  let p0 := staged world source policy 0 2 entry
  let samePolicy := staged world source policy 0 2 other
  let q0 := staged world futureSource futurePolicy 0 4 other
  checkStale [p0,samePolicy] world
  let p1 := staged world source policy 2 4 entry
  let q1 := staged world futureSource futurePolicy 2 4 other
  checkStale [p1,q1,q0] world
  let failed := staged world source {policy with budget := policy.expected-1} 4 4 other
  let winner := staged world source policy 4 4 entry
  let challenger := staged world futureSource futurePolicy 4 4 other
  match Functional.RecursiveCompetition.run [failed] world with
  | ([receipt],kept) =>
    match receipt.outcome with
    | .error (.rejected (.approval "joint refusal")) =>
      unless sameWorld kept world && sameWorld receipt.world world do throw "joint refusal state"
    | _ => throw "joint refusal phase"
  | _ => throw "lost refusal receipt"
  let pending := history ++ [p0,samePolicy,q0,p1,q1]
  let (trace,installed) := Functional.RecursiveCompetition.run
    (pending ++ [failed,winner,challenger,winner]) world
  unless trace.length == pending.length+4 && (trace.take pending.length).all (fun receipt =>
      match receipt.outcome with
      | .error .stale => sameWorld receipt.world world
      | _ => false) do throw "historical receipt overwritten"
  match trace.drop pending.length with
  | [refused,won,challenged,replayed] =>
    match refused.outcome,won.outcome,challenged.outcome,replayed.outcome with
    | .error (.rejected (.approval "joint refusal")),.ok (.error "policy"),.error .stale,.error .stale =>
      unless sameWorld refused.world world && sameWorld won.world installed &&
          sameWorld challenged.world installed && sameWorld replayed.world installed do throw "per-attempt head"
    | _,_,_,_ => throw "competing outcome phases"
  | _ => throw "lost attempt receipt"
  unless installed.graph.revision == world.graph.revision+1 &&
      installed.graph.value.metadata.token == policy.token &&
      (installed.graph.value.graph.graph.payload 11).total == policy.expected do throw "wrong winning pair"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source) installed.graph.value.graph.epochs 11
      (world.graph.value.graph.graph.canonical 11)) do throw "dirty reference revived"
  match RecursivePublication.observe installed entry effect with
  | (.ok _,next) =>
    unless next.contexts entry == world.contexts entry+1 && next.contexts other == world.contexts other do
      throw "entry effect retry"
    return (next,[winner,challenger,failed] ++ history)
  | _ => throw "fresh bound evidence refused"

/-- Match Gerbil's eight distinct current/future proposals and shared dependencies. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let initial : World := ⟨⟨0,⟨first,⟨0,82,200⟩⟩⟩,fun entry => entry.val*100⟩
  let intents := ([1,2,3,0,1,2,5,6].zip (List.range 8)).map (fun (stage,index) =>
    let source : RecursiveTopologies.Source := ⟨stage,false⟩
    (source,({token := index+1,expected := RecursiveTopologies.reportTotal source,budget := 200} : Policy)))
  let pairs := intents.zip (intents.drop 1 ++ intents.reverse.take 1)
  let (last,history) ← pairs.foldlM round (initial,[])
  unless last.graph.revision == 8 && history.length == 24 && (last.graph.value.graph.graph.payload 11).total == 135 &&
      ((List.finRange 3).map (fun entry => last.contexts entry - entry.val*100)) == [3,3,2] do throw "final state"
  unless last.graph.value.graph.graph.canonical 12 == first.graph.canonical 12 do throw "independent cache lost"
  checkStale history last

#print axioms Functional.RecursiveCompetition.trace_length
#print axioms Functional.RecursiveCompetition.refused_prefix
#print axioms Functional.RecursiveCompetition.late_refusal_prefix
#print axioms Functional.RecursiveCompetition.obsolete_batch
#print axioms Functional.RecursiveCompetition.submit_revision_monotone
#print axioms Functional.RecursiveCompetition.run_revision_monotone
#print axioms Functional.RecursiveCompetition.historical_stale
#print axioms Functional.RecursiveCompetition.after_winner_obsolete
#eval match test with
  | .ok () => IO.println "RECURSIVE-COMPETITION-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveCompetition
