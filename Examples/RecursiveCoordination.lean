import Examples.Support.RecursiveApprovals
import LeanPoo.Functional.RecursiveCoordination

/-! One live survivor and two repeatedly failing/rejoining names share the actual
checked SCC graph. Incarnation fences and approval/head guards remain distinct.
The host scope/exception protocol is separately exercised in Gerbil controls. -/
namespace LeanPoo.Examples.RecursiveCoordination
open Functional LeanPoo.Examples.RecursiveApprovals
abbrev Name := Fin 3
abbrev Lease := Functional.RecursiveCoordination.Lease Name
abbrev Fleet := Functional.RecursiveCoordination.Fleet Name Bundle Entry Nat
abbrev Submission := Functional.RecursiveCompetition.Submission Bundle Nat
  (Functional.RecursiveApprovals.Failure String String) Entry Nat String Evidence
abbrev Owned := Lease × Submission

/-- Finite receipts count actual attempts, never lifecycle-only exits or starts. -/
structure Execution where
  fleet : Fleet
  attempts : Nat := 0
  installs : Nat := 0

/-- Explicit rejoining obtains a new per-name identity against the current owner. -/
def start (execution : Execution) (name : Name) : Except String (Lease × Execution) :=
  match Functional.RecursiveCoordination.start execution.fleet name with
  | none => .error "duplicate live name"
  | some (lease,next) => .ok (lease,{execution with fleet := next})

/-- Cleanup affects only this incarnation, preserving the actual installed prefix. -/
def stop (execution : Execution) (lease : Lease) : Execution :=
  {execution with fleet := Functional.RecursiveCoordination.stop execution.fleet lease}

/-- The original stage guard and coordinator identity are captured independently. -/
def staged (execution : Execution) (lease : Lease) (source : RecursiveTopologies.Source)
    (policy : Policy) (stamp : Nat) (entry : Entry) : Owned :=
  (lease,⟨prepare execution.fleet.world source policy stamp,stamp,entry,refusing⟩)

/-- Exact result phases accompany the actual installation count. -/
inductive Phase where | stale | joint | winner

/-- Current guard observation never changes an original request's captured stamp. -/
def attempt (execution : Execution) (owned : Owned) (observed : Nat) (phase : Phase) : Except String Execution := do
  let item := {owned.2 with stamp := observed}
  let (result,next) := Functional.RecursiveCoordination.attempt execution.fleet owned.1 item
  let good := match phase,result with
    | .stale,.error .stale => next.world.graph.revision == execution.fleet.world.graph.revision
    | .joint,.error (.rejected (.approval "joint refusal")) => next.world.graph.revision == execution.fleet.world.graph.revision
    | .winner,.ok (.error "policy") => next.world.graph.revision == execution.fleet.world.graph.revision+1
    | _,_ => false
  unless good do throw "incorrect incarnation/publication phase"
  return ⟨next,execution.attempts+1,execution.installs+(if let .winner := phase then 1 else 0)⟩

/-- Replay externally retained requests after their scopes closed; even unchanged
snapshot/stamp values cannot reactivate those incarnations. -/
def replay (execution : Execution) (history : List Owned) : Except String Execution :=
  history.foldlM (fun current owned => attempt current owned 8 .stale) execution

/-- Each name exits initially, exits during interleaved recovery, then exits again
following competition. A different winner is installed on alternating graph rounds. -/
def round (state : Execution × List Owned)
    (intents : (RecursiveTopologies.Source × Policy) × (RecursiveTopologies.Source × Policy)) :
    Except String (Execution × List Owned) := do
  let (initial,history) := state
  let ((source,policy),(futureSource,futurePolicy)) := intents
  let world := initial.fleet.world
  let entry : Entry := ⟨world.graph.revision%3,by omega⟩
  let even := world.graph.revision%2 == 0
  let (a0,e0) ← start initial 0
  let firstA := [staged e0 a0 source policy 0 entry,staged e0 a0 futureSource futurePolicy 0 entry]
  let (b0,e1) ← start (stop e0 a0) 1
  let firstB := [staged e1 b0 source policy 0 entry,staged e1 b0 futureSource futurePolicy 0 entry]
  let (a1,e2) ← start (stop e1 b0) 0
  let (b1,e3) ← start e2 1
  let ap := staged e3 a1 source policy 0 entry
  let bp := staged e3 b1 source policy 0 entry
  let e4 ← attempt e3 ap 2 .stale
  let e5 ← attempt e4 bp 2 .stale
  let aq := staged e5 a1 source policy 2 entry
  let bq := staged e5 b1 futureSource futurePolicy 2 entry
  let e6 ← attempt e5 aq 4 .stale
  let e7 ← attempt e6 bq 4 .stale
  let e8 := stop e7 b1
  unless e8.fleet.live 0 && e8.fleet.live 2 do throw "peer exit closed survivor"
  let (a2,e9) ← start (stop e8 a1) 0
  let (b2,e10) ← start e9 1
  let retired := firstA ++ firstB ++ [ap,bp,aq,bq] ++ history
  let e11 ← replay e10 retired
  let bad := staged e11 a2 source {policy with budget := policy.expected-1} 4 entry
  let e12 ← attempt e11 bad 4 .joint
  let driftA := staged e12 a2 source policy 4 entry
  let driftB := staged e12 b2 source policy 4 entry
  let e13 ← attempt e12 driftA 6 .stale
  let e14 ← attempt e13 driftB 6 .stale
  let freshA := staged e14 a2 source policy 6 entry
  let freshB := staged e14 b2 source policy 6 entry
  let (winner,loser,losingLease) := if even then (freshA,freshB,b2) else (freshB,freshA,a2)
  let e15 ← attempt e14 winner 6 .winner
  let e16 ← attempt e15 loser 6 .stale
  let retry := staged e16 losingLease source {policy with budget := policy.expected-1} 6 entry
  let e17 ← attempt e16 retry 6 .joint
  let future := staged e17 losingLease futureSource futurePolicy 6 entry
  let e18 ← attempt e17 future 8 .stale
  let closed := stop (stop e18 b2) a2
  let all := [bad,driftA,driftB,freshA,freshB,retry,future] ++ retired
  let e19 ← replay closed all
  unless e19.fleet.world.graph.revision == world.graph.revision+1 &&
      e19.fleet.world.graph.value.metadata.token == policy.token &&
      !(RecursiveMigration.recognizes (RecursiveTopologies.names source)
        e19.fleet.world.graph.value.graph.epochs 11 (world.graph.value.graph.graph.canonical 11)) do throw "wrong whole prefix"
  match RecursivePublication.observe e19.fleet.world entry effect with
  | (.ok _,next) =>
    unless (List.finRange 3).all (fun key => next.contexts key == world.contexts key+(if key == entry then 1 else 0)) do
      throw "refine/bound evidence retry"
    return ({e19 with fleet := {e19.fleet with world := next}},all)
  | _ => throw "current evidence refused"

/-- Eight actual SCC/provider/computed rounds retain 24 incarnations per failing
name, one long-lived survivor, and 1112 separately checked publication attempts. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let world : World := ⟨⟨0,⟨first,⟨0,82,200⟩⟩⟩,fun _ => 0⟩
  let (survivor,initial) ← start ⟨⟨world,fun _ => 0,fun _ => false⟩,0,0⟩ 2
  let intents := ([1,2,3,0,1,2,5,6].zip (List.range 8)).map (fun (stage,index) =>
    let source : RecursiveTopologies.Source := ⟨stage,false⟩
    (source,({token := index+1,expected := RecursiveTopologies.reportTotal source,budget := 200} : Policy)))
  let (last,history) ← (intents.zip (intents.drop 1 ++ intents.reverse.take 1)).foldlM round (initial,[])
  let finished := stop last survivor
  unless finished.attempts == 1112 && finished.installs == 8 && history.length == 120 &&
      ((List.finRange 3).map finished.fleet.generation) == [24,24,1] &&
      (List.finRange 3).all (fun name => !finished.fleet.live name) &&
      ((List.finRange 3).map finished.fleet.world.contexts) == [3,3,2] &&
      finished.fleet.world.graph.value.graph.graph.canonical 12 == first.graph.canonical 12 &&
      (finished.fleet.world.graph.value.graph.graph.payload 11).total == 135 do throw "final coordination state"

#print axioms Functional.RecursiveCoordination.start_busy
#print axioms Functional.RecursiveCoordination.start_idle
#print axioms Functional.RecursiveCoordination.stop_world
#print axioms Functional.RecursiveCoordination.stop_other
#print axioms Functional.RecursiveCoordination.old_stop
#print axioms Functional.RecursiveCoordination.closed_refused
#print axioms Functional.RecursiveCoordination.generation_refused
#print axioms Functional.RecursiveCoordination.step_generation_monotone
#print axioms Functional.RecursiveCoordination.run_generation_monotone
#print axioms Functional.RecursiveCoordination.step_revision_monotone
#print axioms Functional.RecursiveCoordination.run_revision_monotone
#print axioms Functional.RecursiveCoordination.historical_refused
#eval match test with
  | .ok () => IO.println "RECURSIVE-COORDINATION-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveCoordination
