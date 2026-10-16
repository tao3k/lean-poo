import LeanPoo.Examples.JointReceipts
import LeanPoo.Functional.JointGenerations

/-! Mixed historical expected heads share one installation order with current
valid alternatives and a drifted receipt. All heads retain actual closure proofs. -/
namespace LeanPoo.Examples.JointGenerations
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
open LeanPoo.Examples.JointReceipts
/-- Enumerate all orders of current valid alternatives, a current drifted receipt,
and near/far historical receipts; only a whole current-generation candidate wins. -/
def round (prior : State × List Attempt) (row : Nat × Head × Nat × Nat) : Except String (State × List Attempt) := do
  let (current,history) := prior
  let (id,head,ceiling,budget) := row
  let ca : State := ⟨id*2,fun _ => head,fun _ => (ceiling,budget)⟩
  let cb : State := ⟨id*2+1,fun _ => head,fun _ => (ceiling,budget+2)⟩
  let a ← certify current.id ca 1
  let b ← certify current.id cb 1
  let bad ← certify current.id ca 0
  let ia : Attempt := ⟨a,1⟩
  let ib : Attempt := ⟨b,1⟩
  let drift : Attempt := ⟨bad,1⟩
  let old := history.take 1 ++ history.reverse.take 1
  let base := [[drift,ia,ib],[drift,ib,ia],[ia,drift,ib],
               [ib,drift,ia],[ia,ib,drift],[ib,ia,drift]]
  -- Insert each historical receipt in every position of every current order.
  let orders := old.foldl (fun orders prior => orders.flatMap (fun order =>
    (List.range (order.length+1)).map (fun pos => order.take pos ++ prior :: order.drop pos))) base
  let results := orders.map (Functional.JointPublication.installSequence current)
  unless results.all (fun state => approved state &&
      ((state.id == ca.id && state.approvals 0 == ca.approvals 0) ||
       (state.id == cb.id && state.approvals 0 == cb.approvals 0))) do
    throw "historical generation or mixed metadata won"
  let .some next := results.head? | throw "no mixed order"
  pure (next,history ++ [ia,ib])
/-- Six actual bridge/deletion/split/restoration rounds retain old receipts while
fresh candidates are explicitly certified against the latest whole snapshot. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merge closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restore closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let rows := [(1,merged,24,48),(2,replaced,16,32),(3,restored,12,24),
               (4,merged,24,48),(5,replaced,16,32),(6,restored,12,24)]
  let result : Except String (State × List Attempt) :=
    rows.foldl (fun prior row => prior.bind (fun state => round state row)) (.ok (initial,[]))
  let .ok (final,history) := result | throw "mixed generation trace refused"
  let replay := Functional.JointPublication.installSequence final history
  unless replay.id == final.id && (final.id == 12 || final.id == 13) &&
      (replay.heads 0).graph.members 7 == [] do throw "old round revived after support restoration"
#eval match check with
  | .ok () => IO.println "JOINT-GENERATIONS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.installSequence_inert
#print axioms Functional.JointPublication.installSequence_mixed_winner
end LeanPoo.Examples.JointGenerations
