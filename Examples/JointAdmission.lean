import LeanPoo.Examples.JointTopology

/-! Locally accepted but jointly refused requests preserve sibling freshness.
All carriers below retain actual sources, discovered SCCs and closure equations. -/
namespace LeanPoo.Examples.JointAdmission
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
/-- Stage actual typed head/policy replacements and both levels of approval. -/
def stage (current : State) (id : Nat) (a b : Head) (ceiling budget : Nat) :=
  let revision : Functional.JointPublication.Revision current :=
    ⟨id,[⟨0,a⟩,⟨1,b⟩],[⟨0,(ceiling,budget)⟩],by simp,by simp⟩
  Functional.JointPublication.prepare (List.finRange 2) localApproved jointApproved current.id revision.apply
/-- Execute interleavings with rejected budgets, a rival winner, SCC reorganization
and a value round trip. Denials never advance the source snapshot identity. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merged closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restored closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let denied := stage initial 1 merged compact 24 35
  let winner := stage initial 2 merged compact 24 36
  let sibling := stage initial 3 compact merged 24 36
  unless (List.finRange 2).all (localApproved denied.candidate) && !jointApproved denied.candidate do
    throw "first denial did not isolate joint admission"
  let next := Functional.JointPublication.run initial [denied,denied,winner,sibling,denied]
  unless next.id == 2 && (next.heads 0).graph.keys.length == 12 && (next.heads 1).graph.keys.length == 10 do
    throw "refusal consumed sibling freshness or stale candidate overwrote winner"
  let second := stage next 4 replaced merged 24 39
  let retry := stage next 5 replaced merged 24 40
  unless (List.finRange 2).all (localApproved second.candidate) && !jointApproved second.candidate do
    throw "split/merge denial did not isolate joint admission"
  let both := Functional.JointPublication.run next [second,sibling,retry,second,winner]
  unless both.id == 5 && (both.heads 0).graph.members 4 == [] && ((both.heads 1).graph.members 2).length == 7 do
    throw "cross-round split/merge interleaving mismatch"
  let mixed := stage both 6 restored replaced 16 28
  let crossed := Functional.JointPublication.run both [mixed,retry,second]
  let roundTrip := stage crossed 7 restored restored 12 24
  let final := Functional.JointPublication.run crossed [roundTrip,denied,winner,sibling,retry,mixed]
  unless final.id == 7 && (final.heads 0).graph.keys.length == 10 && final.approvals 0 == (12,24) do
    throw "equal policy/support values revived an earlier request"
  let fresh := stage final 8 merged compact 24 36
  let accepted := Functional.JointPublication.run final [fresh]
  unless accepted.id == 8 && approved accepted do throw "fresh restaging failed"
#eval match check with
  | .ok () => IO.println "JOINT-ADMISSION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.admitted_iff
#print axioms Functional.JointPublication.admitted_endpoint
#print axioms Functional.JointPublication.joint_refused
#print axioms Functional.JointPublication.run_denied_prefix
#print axioms Functional.JointPublication.run_denied_between
#print axioms Functional.JointPublication.stale_batch
end LeanPoo.Examples.JointAdmission
