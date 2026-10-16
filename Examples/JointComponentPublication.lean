import LeanPoo.Examples.ComponentRounds
import LeanPoo.Functional.JointPublication

/-! Actual source closure feeds a whole metadata/head installation. No projection
is installed separately; abstract identities are fixture values only. -/
namespace LeanPoo.Examples.JointComponentPublication
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds
/-- Two endpoint heads and two approval objects share one authoritative bundle. -/
abbrev State := Functional.JointPublication.Bundle Nat (Fin 2) (Fin 2)
  (fun _ => Vector Nat 12) (fun _ => Nat × Bool)
/-- Construct the example bundle with independent typed head and policy fields. -/
def bundle (id : Nat) (raw : Vector Nat 12) (limit : Nat) : State :=
  ⟨id,fun _ => raw,fun _ => (limit,true)⟩
/-- Both current services and their exact candidate metadata must jointly agree. -/
def approved (spec : Declaration Key Values) (candidate : State) : Bool :=
  (List.finRange 2).all (fun key =>
    ComponentRounds.approved spec (candidate.approvals key).2 true (candidate.approvals key).1 (candidate.heads key)) &&
  decide ((candidate.heads 0).get 10 = (candidate.heads 1).get 10)
/-- Close real source programs, refuse a candidate metadata/head bundle, then
freshly prepare and install the entire approved bundle without mixed projections. -/
def check : Except String Unit := do
  let initialRaw ← execute source
  let .ok merged := SupportRevision.join source (contributions .merge) | throw "joint merge refused"
  let mergedRaw ← execute merged.apply
  let initial := bundle 0 initialRaw 12
  let denied := bundle 1 mergedRaw 12
  let held := Functional.JointPublication.install 0 initial denied (approved merged.apply denied)
  unless held.id == 0 && (held.heads 0).get 10 == 12 && (held.approvals 0).1 == 12 do
    throw "joint refusal exposed partial policy/head state"
  let candidate := bundle 2 mergedRaw 24
  let next := Functional.JointPublication.install held.id held candidate (approved merged.apply candidate)
  unless next.id == 2 && (next.heads 0).get 10 == 24 && (next.heads 1).get 10 == 24 &&
      (next.approvals 0).1 == 24 && (next.approvals 1).1 == 24 do throw "whole joint installation mismatch"
  let stale := Functional.JointPublication.install 0 next denied true
  unless stale.id == 2 && (stale.approvals 0).1 == 24 do throw "stale request overwrote whole winner"
  let .ok split := SupportRevision.joinAt next.id 2 merged.apply (contributions .replace) |
    throw "fresh current source revision refused"
  let splitRaw ← execute split.apply
  let finalCandidate := bundle 3 splitRaw 30
  let final := Functional.JointPublication.install next.id next finalCandidate (approved split.apply finalCandidate)
  unless final.id == 3 && (final.heads 0).get 10 == 16 && (final.heads 1).get 10 == 16 &&
      (final.approvals 0).1 == 30 do throw "fresh joint restaging mismatch"
#eval match check with
  | .ok () => IO.println "JOINT-PUBLICATION-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.whole
#print axioms Functional.JointPublication.refused
#print axioms Functional.JointPublication.stale
#print axioms Functional.JointPublication.commit
#print axioms Functional.JointPublication.valid
end LeanPoo.Examples.JointComponentPublication
