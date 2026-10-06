import LeanPoo.Functional.Transformation
import LeanPoo.Functional.CertifiedRequirements

/-! Reuse deterministic witness data and its proof across certified routes. -/
namespace LeanPoo.Functional.Transformation
universe u v

/-- Witness data, indexed by the exact input, together with correctness. -/
def Solution (problem : Problem.{u, v}) (input : problem.Input) :=
  {result : problem.Result input // problem.Correct input result}

/-- Total on valid inputs; existence in Prop alone does not supply this data. -/
def Solver (problem : Problem.{u, v}) :=
  (input : problem.Input) → problem.Valid input → Solution problem input

/-- Extract a target witness and reuse the route's admitted soundness proof. -/
def CertifiedTransformation.pullSolution {A B : Problem.{u, v}}
    (route : CertifiedTransformation A B) (input : A.Input) (valid : A.Valid input)
    (target : Solution B (route.forward input)) : Solution A input :=
  ⟨route.extract input target.val, route.sound input valid target.val target.property⟩

@[simp] theorem CertifiedTransformation.pullSolution_val {A B : Problem.{u, v}}
    (route : CertifiedTransformation A B) (input : A.Input) (valid : A.Valid input)
    (target : Solution B (route.forward input)) :
    (route.pullSolution input valid target).val = route.extract input target.val := rfl

/-- Transport validity forward, invoke the supplied solver, then extract back. -/
def CertifiedTransformation.pullSolver {A B : Problem.{u, v}}
    (route : CertifiedTransformation A B) (target : Solver B) : Solver A :=
  fun input valid => route.pullSolution input valid
    (target (route.forward input) (route.preserves input valid))

@[simp] theorem CertifiedTransformation.pullSolver_val {A B : Problem.{u, v}}
    (route : CertifiedTransformation A B) (target : Solver B)
    (input : A.Input) (valid : A.Valid input) :
    (route.pullSolver target input valid).val = route.extract input
      (target (route.forward input) (route.preserves input valid)).val := rfl

/-- Composed routing needs no new client proof of the final extracted witness. -/
theorem pullSolver_compose {A B C : Problem.{u, v}}
    (first : CertifiedTransformation A B) (second : CertifiedTransformation B C)
    (target : Solver C) :
    (compose first second).pullSolver target = first.pullSolver (second.pullSolver target) := rfl

@[simp] theorem pullSolver_identity (A : Problem.{u, v}) (target : Solver A) :
    (identity A).pullSolver target = target := rfl

end LeanPoo.Functional.Transformation

namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- A joint C4 result contract viewed as an exact-context witness problem. -/
def requirementsProblem (keys : List Key) (Claim : ∀ c, Results Value c keys → Prop) :
    Transformation.Problem.{u, w} where
  Input := Context
  Result := fun c => Results Value c keys
  Valid := fun _ => True
  Correct := Claim

/-- Reuse the retained factories and their joint proof without a provider lookup. -/
def Certified.asSolver {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
    (ready : Certified keys Claim) : Transformation.Solver (requirementsProblem keys Claim) :=
  fun context _ => ready.build context

@[simp] theorem Certified.asSolver_val {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
    (ready : Certified keys Claim) (context : Context) :
    (ready.asSolver context True.intro).val = Requirements.build ready.factories context := rfl

end LeanPoo.Functional.Requirements
