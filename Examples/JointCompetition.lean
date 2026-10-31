import Examples.Support.JointReceipts
import LeanPoo.Functional.JointCompetition

/-! All six lock orders for two valid alternatives and one drifted receipt use
actual certified component heads across six support/SCC revision rounds. -/
namespace LeanPoo.Examples.JointCompetition
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
open LeanPoo.Examples.JointReceipts
/-- Enumerate either valid winner with a drifted attempt before, between or after.
The state advanced for the next fixture round is one permitted scheduler order. -/
def round (current : State) (row : Nat × Head × Nat × Nat) : Except String State := do
  let (id,head,ceiling,budget) := row
  let ca : State := ⟨id*2,fun _ => head,fun _ => (ceiling,budget)⟩
  let cb : State := ⟨id*2+1,fun _ => head,fun _ => (ceiling,budget+2)⟩
  let a ← certify current.id ca 1
  let b ← certify current.id cb 1
  let bad ← certify current.id ca 0
  let ia : Attempt := ⟨a,1⟩
  let ib : Attempt := ⟨b,1⟩
  let drift : Attempt := ⟨bad,1⟩
  let orders := [[drift,ia,ib],[drift,ib,ia],[ia,drift,ib],
                 [ib,drift,ia],[ia,ib,drift],[ib,ia,drift]]
  let results := orders.map (Functional.JointPublication.installSequence current)
  unless results.all (fun state => approved state &&
      ((state.id == ca.id && state.approvals 0 == ca.approvals 0) ||
       (state.id == cb.id && state.approvals 0 == cb.approvals 0))) do
    throw "scheduler order produced mixed or unapproved winner"
  let .some next := results.head? | throw "no scheduler order"
  pure next
/-- Reuse concrete bridge addition, endpoint removal, SCC split and restoration;
both valid-winner identities are checked at every lifecycle step. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merge closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restored closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let rows := [(1,merged,24,48),(2,replaced,16,32),(3,restored,12,24),
               (4,merged,24,48),(5,replaced,16,32),(6,restored,12,24)]
  let result : Except String State := rows.foldl (fun prior row => prior.bind (fun state => round state row)) (.ok initial)
  let .ok final := result | throw "competing topology trace refused"
  unless final.id == 12 && (final.heads 0).graph.members 7 == [] do throw "final component erasure mismatch"
#eval match check with
  | .ok () => IO.println "JOINT-COMPETITION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.installSequence_winner
#print axioms Functional.JointPublication.competing_orders
#print axioms Functional.JointPublication.receipt_replay_refused
end LeanPoo.Examples.JointCompetition
