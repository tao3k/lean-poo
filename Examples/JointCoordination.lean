import LeanPoo.Examples.JointReceipts
import LeanPoo.Functional.CoordinatorRejoining

/-! Independent preparation factories share an observed head, reject shared
guard drift, then compete. Actual component heads cover six source/SCC phases. -/
namespace LeanPoo.Examples.JointCoordination
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
open LeanPoo.Examples.JointReceipts
/-- Independent factories reobserve the unchanged head after shared metadata refusals;
either valid candidate may win, but the superseded competitor must stay stale. -/
def round (prior : State × List Attempt) (row : Head × Nat × Nat) : Except String (State × List Attempt) := do
  let (current,history) := prior
  let (head,ceiling,budget) := row
  let ta ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget)⟩ 1
  let tb ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget+2)⟩ 2
  let tc ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget+4)⟩ 3
  let td ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget+6)⟩ 4
  let shared : Receipt := ⟨current.id,ta.candidate,0,ta.valid⟩
  let denied : List Attempt := [⟨shared,1⟩,⟨shared,1⟩]
  let recovering : List (Functional.JointPublication.CoordinatorEvent (Revision := Nat) String
      (fun state : State => approved state = true)) :=
    [.attempt ⟨shared,1⟩,.stopped "failed",.attempt ⟨shared,1⟩,.rejoined "failed"]
  let a := Functional.JointPublication.restageAfter current
    (Functional.JointPublication.coordinatorAttempts recovering) (freshCandidate ta) 1
  let b := Functional.JointPublication.restageAfter current denied (freshCandidate tb) 2
  unless a.expected == current.id && b.expected == current.id do throw "refusal moved coordinator source"
  let ia : Attempt := ⟨a,1⟩
  let ib : Attempt := ⟨b,2⟩
  let left := Functional.JointPublication.installSequence current (denied ++ [ia,ib] ++ history)
  let right := Functional.JointPublication.installSequence current (denied ++ [ib,ia] ++ history)
  unless left.id == current.id+1 && left.approvals 0 == (ceiling,budget) &&
      right.id == current.id+1 && right.approvals 0 == (ceiling,budget+2) do
    throw "coordinator order produced mixed candidate or old winner"
  -- Lifecycle exits carry no installation; survivors still select the full
  -- fresh winner after guard refusals, and exits after publication cannot undo it.
  let events : List (Functional.JointPublication.CoordinatorEvent (Revision := Nat) String (fun state : State => approved state = true)) :=
    [.attempt ⟨shared,1⟩,.stopped "failed",.attempt ⟨shared,1⟩,.rejoined "failed",.stopped "returned",
     .attempt ia,.stopped "after-publication",.attempt ib] ++ history.map .attempt
  let recovered := Functional.JointPublication.installCoordinated current events
  unless recovered.id == left.id && recovered.approvals 0 == left.approvals 0 do
    throw "local exit cancelled survivors or rolled back publication"
  let oldHead := Functional.JointPublication.installCoordinated left
    [.rejoined "failed",.attempt ib]
  let oldGuard := Functional.JointPublication.installCoordinated current
    [.rejoined "failed",.attempt (⟨shared,1⟩ : Attempt)]
  unless oldHead.id == left.id && oldHead.approvals 0 == left.approvals 0 &&
      oldGuard.id == current.id && oldGuard.approvals 0 == current.approvals 0 do
    throw "rejoining revived superseded head or expired shared guard"
  -- Multiple names recover in different lifecycle orders. Archived receipts
  -- mix previous head generations with current-head shared-guard refusal.
  let waves : List (List (Functional.JointPublication.CoordinatorEvent (Revision := Nat) String
      (fun state : State => approved state = true))) :=
    [[.stopped "c",.stopped "d",.rejoined "c",.rejoined "d"],
     [.stopped "d",.rejoined "d",.stopped "c",.rejoined "c"]]
  let oldAttempts := denied ++ history
  let c := Functional.JointPublication.restageAfter current oldAttempts (freshCandidate tc) 3
  let d := Functional.JointPublication.restageAfter current oldAttempts (freshCandidate td) 4
  let ic : Attempt := ⟨c,3⟩
  let id : Attempt := ⟨d,4⟩
  let competitors := [ia,ib,ic,id]
  for wave in waves do
    let replayEvents := wave ++ oldAttempts.map .attempt
    let observed := Functional.JointPublication.installCoordinated current replayEvents
    unless observed.id == current.id && observed.approvals 0 == current.approvals 0 do
      throw "interleaved recovery revived a historical receipt"
    for first in List.range 4 do
      let order := competitors.drop first ++ competitors.take first
      let winner := Functional.JointPublication.installCoordinated current
        (replayEvents ++ order.map .attempt ++ wave ++ oldAttempts.map .attempt)
      unless winner.id == current.id+1 && winner.approvals 0 == (ceiling,budget+2*first) do
        throw "four-way recovery competition mixed a winner or lost fresh preparation"
  -- Recovery can fail before a receipt exists, repeatedly and across names.
  -- Only explicit success creates a current checked candidate for installation.
  let failedC := Functional.JointPublication.prepareRejoining (Error := String) current
    (fun _ => .error "c preparation failed") 3
  let failedD := Functional.JointPublication.prepareRejoining (Error := String) current
    (fun _ => .error "d preparation failed") 4
  let readyC := Functional.JointPublication.prepareRejoining (Error := String) current
    (fun state => .ok (freshCandidate tc state)) 3
  let readyD := Functional.JointPublication.prepareRejoining (Error := String) current
    (fun state => .ok (freshCandidate td state)) 4
  let errors : List (Except String Attempt) :=
    [failedC.map (fun receipt => ⟨receipt,3⟩),failedD.map (fun receipt => ⟨receipt,4⟩),
     failedC.map (fun receipt => ⟨receipt,3⟩),failedD.map (fun receipt => ⟨receipt,4⟩)]
  let .error messageC := failedC | throw "failed preparation minted a receipt"
  let .error messageD := failedD | throw "failed preparation minted a receipt"
  unless messageC == "c preparation failed" && messageD == "d preparation failed" do
    throw "preparation changed the original error"
  let stagedC : Except String Attempt := readyC.map (fun receipt => ⟨receipt,3⟩)
  let stagedD : Except String Attempt := readyD.map (fun receipt => ⟨receipt,4⟩)
  let oldResults : List (Except String Attempt) := oldAttempts.map .ok
  let retriedC := Functional.JointPublication.installRejoining current
    (errors ++ oldResults ++ [stagedC,stagedD] ++ errors)
  let retriedD := Functional.JointPublication.installRejoining current
    (errors.reverse ++ oldResults.reverse ++ [stagedD,stagedC] ++ errors)
  unless retriedC.id == current.id+1 && retriedC.approvals 0 == (ceiling,budget+4) &&
      retriedD.id == current.id+1 && retriedD.approvals 0 == (ceiling,budget+6) do
    throw "failed recovery rolled back a winner or cancelled a fresh peer"
  let late := Functional.JointPublication.installChecked b.expected left b.candidate (2:Nat) 2 true
  unless late.id == left.id && late.approvals 0 == left.approvals 0 do throw "superseded coordinator overwrote winner"
  pure (left,history ++ denied ++ [ia,ib,ic,id])
/-- Fresh per-round factories use certified merge/delete/split/restore sources. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merge closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restore closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let rows := [(merged,24,48),(replaced,16,32),(restored,12,24),
               (merged,24,48),(replaced,16,32),(restored,12,24)]
  let result : Except String (State × List Attempt) :=
    rows.foldl (fun prior row => prior.bind (fun state => round state row)) (.ok (initial,[]))
  let .ok (final,history) := result | throw "coordinator trace refused"
  let replay := Functional.JointPublication.installSequence final history
  unless replay.id == 6 && replay.approvals 0 == (12,24) &&
      (replay.heads 0).graph.members 7 == [] do throw "cross-round coordinator revival"
#eval match check with
  | .ok () => IO.println "JOINT-COORDINATION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.restageAfter_competing
#print axioms Functional.JointPublication.restageAfter_superseded
#print axioms Functional.JointPublication.restageAfter_refused
#print axioms Functional.JointPublication.installCoordinated_stopped
#print axioms Functional.JointPublication.restageAfter_coordinator_stopped
#print axioms Functional.JointPublication.installCoordinated_valid
#print axioms Functional.JointPublication.installCoordinated_rejoined
#print axioms Functional.JointPublication.restageAfter_rejoined_expected
#print axioms Functional.JointPublication.rejoined_receipt_refused
#print axioms Functional.JointPublication.coordinatorAttempts_lifecycle
#print axioms Functional.JointPublication.installCoordinated_recoveryWave
#print axioms Functional.JointPublication.recoveryWave_refused
#print axioms Functional.JointPublication.restageAfter_recoveryWave
#print axioms Functional.JointPublication.prepareRejoining_failed
#print axioms Functional.JointPublication.prepareRejoining_success
#print axioms Functional.JointPublication.installRejoining_failed
#print axioms Functional.JointPublication.installRejoining_valid
end LeanPoo.Examples.JointCoordination
