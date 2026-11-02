import Examples.Support.ComponentRounds
import LeanPoo.Functional.JointRevision
import LeanPoo.Functional.JointAdmission

/-! Shared actual component heads for asymmetric joint publication controls. -/
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
/-- Both typed service heads share a per-service ceiling and total budget. -/
abbrev State := Functional.JointPublication.Bundle Nat (Fin 2) (Fin 1) (fun _ => Head) (fun _ => Nat × Nat)
/-- Each endpoint checks actual support, equations and proposed local ceiling. -/
def localApproved (state : State) (key : Fin 2) : Bool :=
  ComponentRounds.approved (state.heads key).spec true true (state.approvals 0).1 (state.heads key).closed.raw
/-- The whole-family budget remains independent of local service ceilings. -/
def jointApproved (state : State) : Bool :=
  decide ((state.heads 0).closed.raw.get 10 + (state.heads 1).closed.raw.get 10 ≤ (state.approvals 0).2)
/-- Enumerate the complete endpoint family before checking their joint budget. -/
def approved (state : State) : Bool :=
  Functional.JointPublication.admitted (List.finRange 2) localApproved jointApproved state
end LeanPoo.Examples.JointTopology
