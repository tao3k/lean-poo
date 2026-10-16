import LeanPoo.Examples.ComponentRounds
import LeanPoo.Functional.JointRevision

/-! Different active component supports/SCCs coexist in one atomic shared-budget
bundle. Every example head retains its actual source and successful equations. -/
namespace LeanPoo.Examples.JointTopology
open Functional.GeneralizedGraph Functional.StrongComponents LeanPoo.Examples.ComponentRounds
/-- Actual endpoint source, discovered support and all component equations. -/
structure Head where
  spec : Declaration Key Values
  graph : Supported (fun key dep => decide (dep ∈ spec.reads key))
  closed : Functional.ComponentExecution.Closed spec
/-- Discover and close the actual submitted source using the shared lens runner. -/
def close (spec : Declaration Key Values) : Except String Head :=
  match discoverSupported spec.keys (fun key dep => decide (dep ∈ spec.reads key)) with
  | none => .error "joint topology discovery refused"
  | some graph =>
    match Functional.ComponentExecution.build spec graph (Vector.replicate 12 0) 32 with
    | .error message => .error message
    | .ok closed => .ok ⟨spec,graph,closed⟩
/-- The shared policy carries per-service ceiling and whole-family total budget. -/
abbrev State := Functional.JointPublication.Bundle Nat (Fin 2) (Fin 1) (fun _ => Head) (fun _ => Nat × Nat)
/-- Endpoint-local equations and the total budget jointly approve different graphs. -/
def approved (state : State) : Bool :=
  let ceiling := (state.approvals 0).1
  let budget := (state.approvals 0).2
  (List.finRange 2).all (fun key =>
    ComponentRounds.approved (state.heads key).spec true true ceiling (state.heads key).closed.raw) &&
  decide ((state.heads 0).closed.raw.get 10 + (state.heads 1).closed.raw.get 10 ≤ budget)
/-- Dependent replacement candidates coexist with component membership revisions;
final joint refusal preserves BOTH old heads and old shared approval metadata. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge source refused"
  let .ok merged := close merge.apply | throw "merged closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split source refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore source refused"
  let .ok restored := close restore.apply | throw "restored closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let first : Functional.JointPublication.Revision initial :=
    ⟨1,[⟨0,merged⟩],[⟨0,(24,36)⟩],by simp,by simp⟩
  let next := Functional.JointPublication.install initial.id initial first.apply (approved first.apply)
  unless next.id == 1 && (next.heads 0).graph.keys.length == 12 && (next.heads 1).graph.keys.length == 10 do
    throw "asymmetric insertion changed sibling support"
  let second : Functional.JointPublication.Revision next :=
    ⟨2,[⟨0,replaced⟩,⟨1,merged⟩],[⟨0,(24,39)⟩],by simp,by simp⟩
  let refused := Functional.JointPublication.install next.id next second.apply (approved second.apply)
  unless refused.id == 1 && (refused.approvals 0).2 == 36 do throw "failed total budget exposed candidate fields"
  let retry : Functional.JointPublication.Revision refused :=
    ⟨3,[⟨0,replaced⟩,⟨1,merged⟩],[⟨0,(24,40)⟩],by simp,by simp⟩
  let both := Functional.JointPublication.install refused.id refused retry.apply (approved retry.apply)
  unless (both.heads 0).graph.members 4 == [] && ((both.heads 1).graph.members 2).length == 7 do
    throw "mixed active SCC membership mismatch"
  unless both.id == 3 && (both.heads 0).closed.raw.get 10 == 16 && (both.heads 1).closed.raw.get 10 == 24 do
    throw "simultaneous split/merge mismatch"
  let third : Functional.JointPublication.Revision both :=
    ⟨4,[⟨0,restored⟩,⟨1,replaced⟩],[⟨0,(16,28)⟩],by simp,by simp⟩
  let final := Functional.JointPublication.install both.id both third.apply (approved third.apply)
  unless final.id == 4 && (final.heads 0).graph.members 7 == [] && (final.heads 1).graph.members 4 == [] do
    throw "component erasure mismatch"
  let stale := Functional.JointPublication.install initial.id final first.apply true
  unless stale.id == 4 && (stale.approvals 0).2 == 28 do throw "old source bundle revived after topology changes"
#eval match check with
  | .ok () => IO.println "JOINT-TOPOLOGY-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.Revision.head_at
#print axioms Functional.JointPublication.Revision.approval_at
#print axioms Functional.JointPublication.Revision.head_frame
#print axioms Functional.JointPublication.Revision.approval_frame
#print axioms SupportRevision.erased
#print axioms Functional.JointPublication.whole
end LeanPoo.Examples.JointTopology
