import Examples.Support.ComponentRounds
import LeanPoo.Functional.JointPublication

/-! Finite interleavings of whole joint bundles share actual component closure.
Identity freshness is a native premise, independent of restored field values. -/
namespace LeanPoo.Examples.JointRounds
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds
/-- Two concrete endpoint carriers share the same dependent bundle abstraction. -/
abbrev State := Functional.JointPublication.Bundle Nat (Fin 2) (Fin 2)
  (fun _ => Vector Nat 12) (fun _ => Nat)
/-- Fixture snapshots have distinct identities even when their fields return. -/
def bundle (id : Nat) (raw : Vector Nat 12) (limit : Nat) : State := ⟨id,fun _ => raw,fun _ => limit⟩
/-- Reuse exact typed source edits and complete residuals on each topology round. -/
def check : Except String Unit := do
  let initialRaw ← execute source
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let mergedRaw ← execute merge.apply
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let splitRaw ← execute split.apply
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let restoredRaw ← execute restore.apply
  unless initialRaw == restoredRaw do throw "actual source round trip mismatch"
  let initial := bundle 0 initialRaw 12
  let winner := bundle 1 mergedRaw 30
  let sibling := bundle 2 mergedRaw 24
  let denied := bundle 3 splitRaw 12
  let next := bundle 4 splitRaw 30
  let restored := bundle 5 restoredRaw 12
  let trace : List (Functional.JointPublication.Request Nat (Fin 2) (Fin 2)
      (fun _ => Vector Nat 12) (fun _ => Nat)) :=
    [⟨0,winner,approved merge.apply true true 30 mergedRaw⟩,
     ⟨0,sibling,true⟩,⟨1,denied,false⟩,
     ⟨1,next,approved split.apply true true 30 splitRaw⟩,
     ⟨4,restored,approved restore.apply true true 12 restoredRaw⟩]
  let final := Functional.JointPublication.run initial trace
  unless final.id == 5 && (final.heads 0).get 10 == 12 && final.approvals 0 == 12 do
    throw "interleaved whole trace mismatch"
  let late := [(winner,true),(sibling,true),(denied,false)]
  let held := late.foldl (fun current request => Functional.JointPublication.install 0 current request.1 request.2) final
  unless held.id == 5 && (held.heads 1).get 10 == 12 do throw "old requests revived after round trip"
  let .ok retry := SupportRevision.joinAt final.id 5 restore.apply (contributions .merge) |
    throw "current source restaging refused"
  let retryRaw ← execute retry.apply
  let candidate := bundle 6 retryRaw 24
  let accepted := Functional.JointPublication.install final.id final candidate
    (approved retry.apply true true 24 retryRaw)
  unless accepted.id == 6 && (accepted.heads 0).get 10 == 24 && accepted.approvals 0 == 24 do
    throw "fresh joint restaging mismatch"
#eval match check with
  | .ok () => IO.println "JOINT-ROUNDS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.stale_batch
#print axioms Functional.JointPublication.run_valid
#print axioms Functional.JointPublication.whole
#print axioms Functional.ComponentExecution.resolved_correct
end LeanPoo.Examples.JointRounds
