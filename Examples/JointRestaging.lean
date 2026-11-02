import Examples.Support.JointReceipts
import LeanPoo.Functional.JointRestaging

/-! Successful preparation observes a newer head while old attempts are pending.
Actual certified source heads cover six declared support/SCC revision phases. -/
namespace LeanPoo.Examples.JointRestaging
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
open LeanPoo.Examples.JointReceipts
/-- A fixture step retains its actual source/closure plus local/joint policy. -/
structure Step where
  head : Head
  ceiling : Nat
  budget : Nat
/-- Advance one source phase, reject changed metadata, then explicitly prepare
the next phase while an old candidate remains absent from the observed prefix. -/
def pair (prior : State × List Attempt) (steps : Step × Step) : Except String (State × List Attempt) := do
  let (current,history) := prior
  let (first,next) := steps
  let primary ← certify current.id ⟨current.id+1,fun _ => first.head,fun _ => (first.ceiling,first.budget)⟩ 1
  let held ← certify current.id primary.candidate 1
  let prefixAttempts : List Attempt := [⟨primary,1⟩]
  let observed := Functional.JointPublication.installSequence current prefixAttempts
  let template ← certify observed.id ⟨0,fun _ => next.head,fun _ => (next.ceiling,next.budget)⟩ 1
  let bad : Attempt := ⟨⟨observed.id,template.candidate,0,template.valid⟩,1⟩
  let checkedPrefix := prefixAttempts ++ [bad] ++ history
  let receipt := Functional.JointPublication.restageAfter current checkedPrefix (freshCandidate template) 1
  unless receipt.expected == observed.id do throw "restaging captured an old source head"
  let fresh : Attempt := ⟨receipt,1⟩
  let old : Attempt := ⟨held,1⟩
  let finishA := Functional.JointPublication.installSequence current (checkedPrefix ++ [old,fresh,old] ++ history)
  let finishB := Functional.JointPublication.installSequence current (checkedPrefix ++ [fresh,old,fresh] ++ history)
  unless finishA.id == observed.id+1 && finishB.id == finishA.id && approved finishA do
    throw "late old work altered freshly staged revision"
  pure (finishA,history ++ prefixAttempts ++ [old,bad,fresh])
/-- Three pairs reuse actual merge/delete/split/restore construction for two cycles. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merge closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restore closure refused"
  let m : Step := ⟨merged,24,48⟩
  let s : Step := ⟨replaced,16,32⟩
  let r : Step := ⟨restored,12,24⟩
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let result : Except String (State × List Attempt) :=
    [(m,s),(r,m),(s,r)].foldl (fun prior row => prior.bind (fun state => pair state row)) (.ok (initial,[]))
  let .ok (final,_) := result | throw "restaging trace refused"
  unless final.id == 6 && final.approvals 0 == (12,24) &&
      (final.heads 0).graph.members 7 == [] do throw "restaging component erasure mismatch"
#eval match check with
  | .ok () => IO.println "JOINT-RESTAGING-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.restageAfter_expected
#print axioms Functional.JointPublication.restageAfter_late
end LeanPoo.Examples.JointRestaging
