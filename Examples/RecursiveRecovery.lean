import Examples.Support.RecursiveApprovals
import LeanPoo.Functional.RecursiveRecovery

/-! Failed scopes release queues; survivors and explicitly recovered coordinators
alternate actual SCC publications. Complete ABA stamps and identity correspondence
are premises; Gerbil separately tests exception payloads and post-cleanup policy. -/
namespace LeanPoo.Examples.RecursiveRecovery
open Functional LeanPoo.Examples.RecursiveApprovals
abbrev Submission := Functional.RecursiveCompetition.Submission Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence
abbrev Session := Functional.RecursiveSubmissions.Session Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence

/-- Capture original request versions separately from the later guard observation. -/
def staged (world : World) (source : RecursiveTopologies.Source) (policy : Policy)
    (stamp : Nat) (entry : Entry) : Submission :=
  ⟨prepare world source policy stamp,stamp,entry,refusing⟩

/-- Append previously prepared requests without rebuilding or refreshing them. -/
def queue (state : Session) (items : List Submission) : Session :=
  items.foldl (fun current item => RecursiveSubmissions.enqueue current (fun _ => item)) state

/-- Expected outcomes distinguish stale guards, joint refusal and installed/effect refusal. -/
inductive Phase where | stale | joint | winner

/-- Inspect each real attempt and its retained receipt; no phase is a generic success. -/
def consume (state : Session) (stamp : Nat) (expected : Phase) : Except String Session := do
  unless !state.pending.isEmpty do throw "empty recovery attempt"
  let next := RecursiveSubmissions.advance state stamp
  match next.receipts.getLast? with
  | none => throw "lost recovery receipt"
  | some receipt =>
    let good := match expected,receipt.outcome with
      | .stale,.error .stale => next.world.graph.revision == state.world.graph.revision
      | .joint,.error (.rejected (.approval "joint refusal")) => next.world.graph.revision == state.world.graph.revision
      | .winner,.ok (.error "policy") => next.world.graph.revision == state.world.graph.revision+1
      | _,_ => false
    unless good do throw "incorrect recovery phase"
    return next

/-- First exit without publishing. After two approval drift windows a survivor
wins odd rounds; a freshly recovered coordinator wins even rounds. Old queues never
resume, although externally retained old requests are explicitly replayed and refused. -/
def round (state : World × List Submission × Nat)
    (intents : (RecursiveTopologies.Source × Policy) × (RecursiveTopologies.Source × Policy)) :
    Except String (World × List Submission × Nat) := do
  let (world,history,count) := state
  let ((source,policy),(futureSource,futurePolicy)) := intents
  let entry : Entry := ⟨world.graph.revision%3,by omega⟩
  let odd := world.graph.revision%2 == 1
  let p0 := staged world source policy 0 entry
  let q0 := staged world futureSource futurePolicy 0 entry
  let abandoned := RecursiveRecovery.finish
    (queue (RecursiveRecovery.restart world) [p0,q0]) (.error "coordinator-exit" : Except String Unit)
  unless abandoned.receipts.isEmpty && abandoned.world.graph.revision == world.graph.revision do
    throw "failed scope installed work"
  let s0 := queue (RecursiveRecovery.restart abandoned.world) [p0,staged world source policy 0 entry]
  let s1 ← ([Phase.stale,.stale]).foldlM (fun current phase => consume current 2 phase) s0
  let s2 := queue s1 [staged s1.world source policy 2 entry,staged s1.world futureSource futurePolicy 2 entry]
  let s3 ← ([Phase.stale,.stale]).foldlM (fun current phase => consume current 4 phase) s2
  let s4 ← (List.replicate history.length Phase.stale).foldlM (fun current phase => consume current 4 phase) (queue s3 history)
  let bad := staged s4.world source {policy with budget := policy.expected-1} 4 entry
  let s5 ← consume (queue s4 [bad]) 4 .joint
  let survivorWinner := staged s5.world source policy 4 entry
  let survivor ← if odd then do
      let s6 ← consume (queue s5 [survivorWinner,staged s5.world futureSource futurePolicy 4 entry]) 4 .winner
      consume s6 4 .stale
    else pure s5
  unless survivor.pending.isEmpty do throw "survivor queue not drained"
  let stopped := RecursiveRecovery.finish survivor (.ok () : Except String Unit)
  let older := [p0,q0] ++ history
  let r0 := queue (RecursiveRecovery.restart stopped.world)
    (older ++ [staged stopped.world source policy 4 entry])
  let r1 ← (List.replicate (older.length+1) Phase.stale).foldlM (fun current phase => consume current 6 phase) r0
  let intent := if odd then {policy with budget := policy.expected-1} else policy
  let fresh := staged r1.world source intent 6 entry
  let r2 ← consume (queue r1 [fresh,p0]) 6 (if odd then .joint else .winner)
  let recovered ← consume r2 6 .stale
  let finished := RecursiveRecovery.finish recovered (.ok (world.graph.revision,"recovered") : Except String (Nat × String))
  unless recovered.pending.isEmpty && finished.world.graph.revision == world.graph.revision+1 &&
      finished.world.graph.value.metadata.token == policy.token &&
      (finished.world.graph.value.graph.graph.payload 11).total == policy.expected do throw "recovery whole pair"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source)
      finished.world.graph.value.graph.epochs 11 (world.graph.value.graph.graph.canonical 11)) do throw "old root revived"
  match RecursivePublication.observe finished.world entry effect with
  | (.ok _,next) =>
    unless (List.finRange 3).all (fun key => next.contexts key ==
        world.contexts key + (if key == entry then 1 else 0)) do throw "recovered bound context"
    return (next,[p0,q0,(if odd then survivorWinner else fresh)] ++ history,
      count+survivor.receipts.length+recovered.receipts.length)
  | _ => throw "recovered refinement/evidence retry"

/-- Eight topology/provider/computed revisions alternate survivors and recovery,
retain 256 attempts and preserve an independent canonical reference across all exits. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let initial : World := ⟨⟨0,⟨first,⟨0,82,200⟩⟩⟩,fun _ => 0⟩
  let intents := ([1,2,3,0,1,2,5,6].zip (List.range 8)).map (fun (stage,index) =>
    let source : RecursiveTopologies.Source := ⟨stage,false⟩
    (source,({token := index+1,expected := RecursiveTopologies.reportTotal source,budget := 200} : Policy)))
  let (last,history,count) ← (intents.zip (intents.drop 1 ++ intents.reverse.take 1)).foldlM round (initial,[],0)
  unless last.graph.revision == 8 && history.length == 24 && count == 256 &&
      ((List.finRange 3).map (fun entry => last.contexts entry)) == [3,3,2] &&
      last.graph.value.graph.graph.canonical 12 == first.graph.canonical 12 &&
      (last.graph.value.graph.graph.payload 11).total == 135 do throw "final recovery state"

#print axioms Functional.RecursiveRecovery.finish_world
#print axioms Functional.RecursiveRecovery.finish_receipts
#print axioms Functional.RecursiveRecovery.finish_outcome
#print axioms Functional.RecursiveRecovery.restart_empty
#print axioms Functional.RecursiveRecovery.recover_current
#print axioms Functional.RecursiveRecovery.survivors_monotone
#print axioms Functional.RecursiveRecovery.recover_after_survivors
#print axioms Functional.RecursiveRecovery.historical_after_exit
#print axioms Functional.RecursiveRecovery.exit_after_late_refusal
#eval match test with
  | .ok () => IO.println "RECURSIVE-RECOVERY-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveRecovery
