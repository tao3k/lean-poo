import Examples.Support.RecursiveApprovals
import LeanPoo.Functional.RecursiveSubmissions

/-! Continuing arrivals reuse the checked eight-service SCC fixture and exact
refine/bind-evidence observers. Stamps abstract complete approval revisions,
including ABA; the Gerbil controls separately exercise scope and exception cleanup. -/
namespace LeanPoo.Examples.RecursiveSubmissions
open Functional LeanPoo.Examples.RecursiveApprovals
abbrev Submission := Functional.RecursiveCompetition.Submission Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence
abbrev Session := Functional.RecursiveSubmissions.Session Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence
abbrev Event := Functional.RecursiveSubmissions.Event Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence

/-- Preparation captures this exact world; the stamp is observed separately on advance. -/
def submission (world : World) (source : RecursiveTopologies.Source) (policy : Policy)
    (captured : Nat) (entry : Entry) : Submission :=
  ⟨prepare world source policy captured,captured,entry,refusing⟩

/-- Admit current/future intents behind the previous round's pending competitors.
Two approval invalidations precede explicit restaging, joint refusal and a winner.
The next round receives both the future challenger and a replayed spent winner. -/
def round (state : Session)
    (intents : (RecursiveTopologies.Source × Policy) × (RecursiveTopologies.Source × Policy)) :
    Except String Session := do
  let ((source,policy),(futureSource,futurePolicy)) := intents
  let entry : Entry := ⟨state.world.graph.revision%3,by omega⟩
  let fresh := fun source policy stamp => (Functional.RecursiveSubmissions.Event.enqueue (fun world => submission world source policy stamp entry) : Event)
  let winner := submission state.world source policy 4 entry
  let script := [fresh source policy 0,fresh futureSource futurePolicy 0] ++
    List.replicate state.pending.length (.advance 2) ++ [.advance 2,
      fresh source policy 2,fresh futureSource futurePolicy 2,.advance 4,.advance 4,
      fresh source {policy with budget := policy.expected-1} 4,
      fresh source policy 4,fresh futureSource futurePolicy 4,
      .advance 4,.advance 4,.advance 4,.enqueue (fun _ => winner)]
  let installed := Functional.RecursiveSubmissions.run script state
  let trace := installed.receipts.drop state.receipts.length
  unless installed.pending.length == 2 && trace.length == state.pending.length+6 do
    throw "continuing FIFO inventory"
  unless trace.take (state.pending.length+4) |>.all (fun receipt =>
      match receipt.outcome with
      | .error .stale => receipt.world.graph.revision == state.world.graph.revision
      | _ => false) do throw "old arrival was refreshed"
  match trace.drop (state.pending.length+4) with
  | [refused,won] =>
    match refused.outcome,won.outcome with
    | .error (.rejected (.approval "joint refusal")),.ok (.error "policy") =>
      unless refused.world.graph.revision == state.world.graph.revision &&
          won.world.graph.revision == state.world.graph.revision+1 do throw "wrong receipt round"
    | _,_ => throw "joint/effect refusal phases"
  | _ => throw "lost continuing receipt"
  unless installed.world.graph.value.metadata.token == policy.token &&
      (installed.world.graph.value.graph.graph.payload 11).total == policy.expected do throw "wrong installed pair"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source)
      installed.world.graph.value.graph.epochs 11 (state.world.graph.value.graph.graph.canonical 11)) do
    throw "old root revived"
  match RecursivePublication.observe installed.world entry effect with
  | (.ok _,next) =>
    unless (List.finRange 3).all (fun key => next.contexts key ==
        state.world.contexts key + (if key == entry then 1 else 0)) do throw "bound entry context"
    return {installed with world := next}
  | _ => throw "fresh effect retry refused"

/-- Eight actual topology/migration/computed revisions keep a live pending suffix;
finishing the scope drains historical competitors without rebuilding the graph. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let initial : Session := ⟨⟨⟨0,⟨first,⟨0,82,200⟩⟩⟩,fun _ => 0⟩,[],[]⟩
  let intents := ([1,2,3,0,1,2,5,6].zip (List.range 8)).map (fun (stage,index) =>
    let source : RecursiveTopologies.Source := ⟨stage,false⟩
    (source,({token := index+1,expected := RecursiveTopologies.reportTotal source,budget := 200} : Policy)))
  let pairs := intents.zip (intents.drop 1 ++ intents.reverse.take 1)
  let last ← pairs.foldlM round initial
  let drained := Functional.RecursiveSubmissions.run [.advance 4,.advance 4] last
  unless drained.pending.isEmpty && drained.receipts.length == 64 && drained.world.graph.revision == 8 &&
      ((List.finRange 3).map (fun entry => drained.world.contexts entry)) == [3,3,2] &&
      (drained.world.graph.value.graph.graph.payload 11).total == 135 &&
      drained.world.graph.value.graph.graph.canonical 12 == first.graph.canonical 12 do throw "final scope state"
  unless (drained.receipts.drop 62).all (fun receipt => match receipt.outcome with
      | .error .stale => true | _ => false) do throw "final competitors revived"

#print axioms Functional.RecursiveSubmissions.enqueue_pending
#print axioms Functional.RecursiveSubmissions.enqueue_preserves
#print axioms Functional.RecursiveSubmissions.empty_advance
#print axioms Functional.RecursiveSubmissions.advance_pending
#print axioms Functional.RecursiveSubmissions.advance_receipts
#print axioms Functional.RecursiveSubmissions.advance_monotone
#print axioms Functional.RecursiveSubmissions.run_monotone
#print axioms Functional.RecursiveSubmissions.historical_stale
#eval match test with
  | .ok () => IO.println "RECURSIVE-SUBMISSIONS-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveSubmissions
