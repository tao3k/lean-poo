import LeanPoo.Functional.FiniteDiagnostics
import LeanPoo.Functional.SolverTransport
open LeanPoo.Functional.Transformation
namespace LeanPoo.Tests.FunctionalFiniteDiagnostics

private def bit (mask position : Nat) : Bool := mask.testBit position
private def spec (mask : Nat) : FiniteSpecification 2 2 :=
  ⟨fun input answer => bit mask (input.val*2+answer.val)⟩
private def forward (mask : Nat) (input : Fin 2) : Fin 2 :=
  if bit mask input.val then 1 else 0
private def extract (mask : Nat) (input answer : Fin 2) : Fin 2 :=
  if bit mask (input.val*2+answer.val) then 1 else 0
-- Independent scalar encoding oracle: no finiteCheck or admitted route calls.
private def scalar (mask position : Nat) : Nat := (mask / 2^position) % 2
private def oracle (s t f e : Nat) : Option (Nat × Nat) :=
  ([0,1].flatMap fun i => [0,1].map fun a => (i,a)).find? fun (i,a) =>
    scalar t (scalar f i*2+a) == 1 && scalar s (i*2+scalar e (i*2+a)) == 0

private def targetSolver : Solver (spec 9).problem := fun input _ =>
  ⟨input, by
    change bit 9 (input.val*2+input.val) = true
    exact Fin.cases (by decide)
      (fun rest => Fin.cases (by decide) (fun impossible => Fin.elim0 impossible) rest) input⟩

private def run : IO Unit := do
  let mut admitted := 0
  let mut refused := 0
  for s in List.range 16 do
    for t in List.range 16 do
      for f in List.range 4 do
        for e in List.range 16 do
          match certifyFiniteOrFailure (spec s) (spec t) (forward f) (extract e), oracle s t f e with
          | .ok route, none =>
            for i in List.finRange 2 do
              unless (route.forward i).val == scalar f i.val do
                throw (IO.userError "admitted forward drift")
              for a in List.finRange 2 do
                unless (route.extract i a).val == scalar e (i.val*2+a.val) do
                  throw (IO.userError "admitted extractor drift")
            admitted := admitted+1
          | .error bad, some (i,a) =>
            unless bad.input.val == i && bad.answer.val == a do
              throw (IO.userError "refusal differs from first scalar counterexample")
            refused := refused+1
          | _, _ => throw (IO.userError "finite admission differs from scalar model")
  unless admitted+refused == 16384 do throw (IO.userError "coverage drift")
  match certifyFiniteOrFailure (spec 9) (spec 9) (forward 1) (extract 5) with
  | .error _ => throw (IO.userError "nontrivial complemented route refused")
  | .ok route =>
    for input in List.finRange 2 do
      let solved := route.pullSolver targetSolver input True.intro
      let answer : Fin 2 := solved.val
      unless answer.val == input.val do throw (IO.userError "admitted route solver drift")
  IO.println "FINITE-DIAGNOSTICS-SOLVER-OK reads=2 complementedRoute=true"
  IO.println s!"FINITE-DIAGNOSTICS-OK routes=16384 admitted={admitted} refused={refused} firstWitness=true"
#eval run

-- Admission is transport soundness, not target-solver existence.
private def emptyTarget : FiniteSpecification 2 2 := ⟨fun _ _ => false⟩
#guard (certifyFiniteOrFailure (spec 0) emptyTarget (forward 0) (extract 0)).isOk
private def noInputs : FiniteSpecification 0 2 := ⟨fun _ _ => false⟩
#guard (certifyFiniteOrFailure noInputs (spec 0) Fin.elim0 (fun _ _ => 0)).isOk
private def noAnswers : FiniteSpecification 2 0 := ⟨fun _ _ => false⟩
#guard (certifyFiniteOrFailure (spec 0) noAnswers (forward 0) (fun _ a => Fin.elim0 a)).isOk
example (bad : FiniteFailure (spec 0) (spec 15) (forward 0) (extract 0)) :
    finiteCheck (spec 0) (spec 15) (forward 0) (extract 0) = false := bad.rejects
example : True := by
  fail_if_success have forged : FiniteFailure (spec 15) (spec 15) (forward 0) (extract 0) :=
    ⟨0, 0, by decide, by decide⟩
  trivial
#print axioms certifyFiniteOrFailure
#print axioms FiniteFailure.rejects
end LeanPoo.Tests.FunctionalFiniteDiagnostics
