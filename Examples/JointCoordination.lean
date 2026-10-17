import LeanPoo.Examples.JointReceipts
import LeanPoo.Functional.JointCoordination

/-! Two independent preparation factories share an observed head, reject shared
guard drift, then compete. Actual component heads cover six source/SCC phases. -/
namespace LeanPoo.Examples.JointCoordination
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
open LeanPoo.Examples.JointReceipts
/-- Both factories reobserve the unchanged head after shared metadata refusals;
either valid candidate may win, but the superseded competitor must stay stale. -/
def round (prior : State × List Attempt) (row : Head × Nat × Nat) : Except String (State × List Attempt) := do
  let (current,history) := prior
  let (head,ceiling,budget) := row
  let ta ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget)⟩ 1
  let tb ← certify current.id ⟨0,fun _ => head,fun _ => (ceiling,budget+2)⟩ 2
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
  let late := Functional.JointPublication.installChecked b.expected left b.candidate (2:Nat) 2 true
  unless late.id == left.id && late.approvals 0 == left.approvals 0 do throw "superseded coordinator overwrote winner"
  pure (left,history ++ denied ++ [ia,ib])
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
end LeanPoo.Examples.JointCoordination
