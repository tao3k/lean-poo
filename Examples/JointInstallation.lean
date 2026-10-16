import LeanPoo.Examples.JointTopology
import LeanPoo.Functional.JointInstallation

/-! Actual certified topology carriers survive post-admission installation races.
Guard revisions below abstract native object identities, not serialized proofs. -/
namespace LeanPoo.Examples.JointInstallation
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
/-- Prepare whole candidates using the existing dependent replacement factory. -/
def candidate (current : State) (id : Nat) (a b : Head) (ceiling budget : Nat) : State :=
  let revision : Functional.JointPublication.Revision current :=
    ⟨id,[⟨0,a⟩,⟨1,b⟩],[⟨0,(ceiling,budget)⟩],by simp,by simp⟩
  revision.apply
/-- A checked candidate can lose to a different SCC topology, or lose only its
metadata revision while the head remains unchanged. Fresh closure then retries. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merged closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restored closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let slow := candidate initial 1 merged compact 24 36
  let rival := candidate initial 2 compact merged 24 36
  unless approved slow && approved rival do throw "joint approval failed before race"
  let winner := Functional.JointPublication.installChecked initial.id initial rival (0:Nat) 0 (approved rival)
  let held := Functional.JointPublication.installChecked initial.id winner slow (0:Nat) 0 (approved slow)
  unless held.id == 2 && (held.heads 0).graph.keys.length == 10 && (held.heads 1).graph.keys.length == 12 do
    throw "late approved topology overwrote rival"
  let next := candidate held 3 merged replaced 24 40
  unless approved next do throw "joint approval failed before metadata drift"
  let refused := Functional.JointPublication.installChecked held.id held next (0:Nat) 1 (approved next)
  unless refused.id == 2 && refused.approvals 0 == (24,36) do throw "metadata drift installed candidate"
  let fresh := candidate refused 4 merged replaced 24 40
  let accepted := Functional.JointPublication.installChecked refused.id refused fresh (1:Nat) 1 (approved fresh)
  unless accepted.id == 4 && (accepted.heads 1).graph.members 4 == [] do throw "fresh split/merge restaging failed"
  let finalCandidate := candidate accepted 5 restored restored 12 24
  let final := Functional.JointPublication.installChecked accepted.id accepted finalCandidate (1:Nat) 1 (approved finalCandidate)
  unless final.id == 5 && (final.heads 0).graph.members 7 == [] do throw "restoration/erasure failed"
#eval match check with
  | .ok () => IO.println "JOINT-INSTALLATION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.checked_whole
#print axioms Functional.JointPublication.checked_requirements
#print axioms Functional.JointPublication.metadata_stale
#print axioms Functional.JointPublication.checked_stale
#print axioms Functional.JointPublication.metadata_retry
end LeanPoo.Examples.JointInstallation
