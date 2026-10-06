import LeanPoo.Functional.SolverTransport
open LeanPoo.Functional
open Requirements Transformation
namespace LeanPoo.Tests.FunctionalSolverTransport
private def Value (c : Nat) : Nat → Type
  | 0 => Fin (c+1)
  | _ => Bool
private def Claim (c : Nat) (data : Results Value c [0,1]) : Prop :=
  data.1.val = c ∧ data.2.1 = (c % 2 == 0)
private def factories : Factories Nat Value [0,1] :=
  ((fun c => ⟨c, Nat.lt_succ_self c⟩), ((fun c => c % 2 == 0), PUnit.unit))
private def ready : Certified [0,1] Claim := certify factories Claim
  (by intro c; exact ⟨rfl,rfl⟩)
private abbrev source : Problem where
  Input := Nat
  Result := fun c => Fin (c+1) × Bool
  Valid := fun c => 0 < c
  Correct := fun c data => data.1.val = c ∧ data.2 = (c % 2 == 0)
private def bridge : CertifiedTransformation source (requirementsProblem [0,1] Claim) where
  forward := id
  preserves := fun _ _ => True.intro
  extract := fun _ data => (data.1, data.2.1)
  sound := fun _ _ _ correct => correct
private def shift : CertifiedTransformation source source where
  forward := fun c => c+2
  preserves := fun c _ => Nat.zero_lt_succ (c+1)
  extract := fun c data => (⟨(data.1.val-2) % (c+1), Nat.mod_lt _ (Nat.zero_lt_succ c)⟩,data.2)
  sound := by
    intro c _ data correct
    change data.1.val = c+2 ∧ data.2 = ((c+2) % 2 == 0) at correct
    rcases correct with ⟨quantity, flag⟩
    constructor
    · change (data.1.val-2) % (c+1) = c
      rw [quantity, Nat.add_sub_cancel, Nat.mod_eq_of_lt (Nat.lt_succ_self c)]
    · have parity : (c+2) % 2 = c % 2 := by simp
      simpa only [parity] using flag
private def run : IO Unit := do
  let target := ready.asSolver
  let routes := [bridge, compose shift bridge, compose (compose shift shift) bridge]
  let mut reads := 0
  for c in List.range 33 do
    if valid : 0 < c then
      for route in routes do
        let solved := route.pullSolver target c valid
        -- Scalar oracle does not apply forward/extract or use the certificates.
        unless solved.val.1.val == c && solved.val.2 == (c % 2 == 0) do
          throw (IO.userError "routed C4 witness differs from independent source answer")
        reads := reads+1
  unless reads == 96 do throw (IO.userError "solver transport coverage drift")
  IO.println s!"FUNCTIONAL-SOLVER-TRANSPORT-OK reads={reads} routes=3 contexts=32 dependentWitness=true jointCertificate=true"
#eval run

example (c : Nat) (valid : source.Valid c) :
    source.Correct c ((compose shift bridge).pullSolver ready.asSolver c valid).val :=
  ((compose shift bridge).pullSolver ready.asSolver c valid).property
example : (compose shift bridge).pullSolver ready.asSolver =
    shift.pullSolver (bridge.pullSolver ready.asSolver) := pullSolver_compose _ _ _
example (_c : Nat) : True := by
  fail_if_success have wrongInput : Solution (requirementsProblem [0,1] Claim) _c :=
    ready.asSolver (_c+1) True.intro
  trivial
example : True := by
  fail_if_success have wrongWitness : Solution source 3 := ⟨(⟨0, by decide⟩,false), by decide⟩
  fail_if_success have invalid : source.Valid 0 := by decide
  trivial
-- An existential proposition cannot be pattern-matched into witness data.
example (P : Problem) (_onlyExists : ∀ a, P.Valid a → ∃ r, P.Correct a r) : True := by
  fail_if_success
    have solver : Solver P := fun a valid =>
      Exists.casesOn (_onlyExists a valid) (fun r correct => ⟨r, correct⟩)
  trivial
#print axioms CertifiedTransformation.pullSolution_val
#print axioms CertifiedTransformation.pullSolver_val
#print axioms pullSolver_compose
#print axioms pullSolver_identity
#print axioms Certified.asSolver_val
end LeanPoo.Tests.FunctionalSolverTransport
