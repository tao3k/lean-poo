import Examples.Support.ComponentRounds

/-! Current approval revisions and competing candidates share actual component
closure. Local revision identities model serial decisions, not native counters. -/
namespace LeanPoo.Examples.ComponentRounds
open Functional.GeneralizedGraph Functional.StrongComponents
/-- Three staged merge candidates and two service revision identities distinguish
approval drift from publication drift. Restaging reuses actual source closure. -/
def approvalCheck : Except String Unit := do
  let .ok staged := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) |
    throw "approval scenario source refused"
  let raw ← execute staged.apply
  let oldRevision : Nat × Nat := (0,0)
  let deniedRevision : Nat × Nat := (0,1)
  let restoredRevision : Nat × Nat := (0,2)
  let candidates : List Nat := [1,2,3]
  let obsolete := candidates.map fun candidate => Functional.ComponentPublication.installChecked
    (0 : Nat) 0 candidate oldRevision restoredRevision (approved staged.apply true true 30 raw)
  unless obsolete.all (fun result => !result.accepted && result.head == 0) do
    throw "changed-back policy revived obsolete candidates"
  let denied := Functional.ComponentPublication.installChecked (0 : Nat) 0 4
    deniedRevision deniedRevision (approved staged.apply true false 30 raw)
  unless !denied.accepted && denied.head == 0 do throw "joint service refusal installed"
  let fresh := Functional.ComponentPublication.installChecked (0 : Nat) denied.head 5
    restoredRevision restoredRevision (approved staged.apply true true 30 raw)
  unless fresh.accepted && fresh.head == 5 do throw "fresh approval preparation refused"
  let late := candidates.map fun candidate => Functional.ComponentPublication.installChecked
    (0 : Nat) fresh.head candidate oldRevision restoredRevision true
  unless late.all (fun result => !result.accepted && result.head == 5) do throw "late sibling lost current winner"
  let .ok split := SupportRevision.joinAt (5 : Nat) fresh.head staged.apply (contributions .replace) |
    throw "restaging current winner refused"
  let splitRaw ← execute split.apply
  let committed := Functional.ComponentPublication.installChecked (5 : Nat) fresh.head 6
    restoredRevision restoredRevision (approved split.apply true true 30 splitRaw)
  unless committed.accepted && committed.head == 6 && splitRaw.get 10 == 16 do
    throw "fresh current-topology split mismatch"
#eval match approvalCheck with
  | .ok () => IO.println "APPROVAL-REVISION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.ComponentPublication.metadata_stale
#print axioms Functional.ComponentPublication.checked_accepted
#print axioms Functional.ComponentPublication.metadata_retry
#print axioms Functional.ComponentPublication.metadata_batch
end LeanPoo.Examples.ComponentRounds
