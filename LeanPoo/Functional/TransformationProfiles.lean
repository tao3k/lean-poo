import LeanPoo.Functional.Transformation

/-! Separate correctness laws for decision, partial, and optimization transport. -/
namespace LeanPoo.Functional.Transformation

universe u v

structure DecisionProblem where
  Input : Type u
  Valid : Input → Prop
  Yes : Input → Prop

structure CertifiedDecisionReduction (A B : DecisionProblem.{u}) where
  forward : A.Input → B.Input
  preserves : ∀ a, A.Valid a → B.Valid (forward a)
  equivalent : ∀ a, A.Valid a → (A.Yes a ↔ B.Yes (forward a))

def CertifiedDecisionReduction.identity (A : DecisionProblem) : CertifiedDecisionReduction A A where
  forward := id
  preserves := fun _ valid => valid
  equivalent := fun _ _ => Iff.rfl

def CertifiedDecisionReduction.compose {A B C : DecisionProblem}
    (f : CertifiedDecisionReduction A B) (g : CertifiedDecisionReduction B C) :
    CertifiedDecisionReduction A C where
  forward := fun a => g.forward (f.forward a)
  preserves := fun a valid => g.preserves _ (f.preserves a valid)
  equivalent := fun a valid => (f.equivalent a valid).trans
    (g.equivalent _ (f.preserves a valid))

theorem decision_compose_equivalent {A B C : DecisionProblem}
    (f : CertifiedDecisionReduction A B) (g : CertifiedDecisionReduction B C)
    (a : A.Input) (valid : A.Valid a) :
    A.Yes a ↔ C.Yes ((f.compose g).forward a) := (f.compose g).equivalent a valid

/-- A successful partial step carries its actual target input and dependent extractor. -/
structure TransportAt (A B : Problem.{u, v}) (a : A.Input) where
  input : B.Input
  preserves : A.Valid a → B.Valid input
  extract : B.Result input → A.Result a
  sound : ∀ _valid : A.Valid a, ∀ r, B.Correct input r → A.Correct a (extract r)

def TransportAt.compose {A B C : Problem} {a : A.Input}
    (f : TransportAt A B a) (g : TransportAt B C f.input) : TransportAt A C a where
  input := g.input
  preserves := fun valid => g.preserves (f.preserves valid)
  extract := fun r => f.extract (g.extract r)
  sound := fun valid r correct => f.sound valid _ (g.sound (f.preserves valid) r correct)

structure CertifiedPartialTransformation (A B : Problem.{u, v}) where
  forward : (a : A.Input) → Option (TransportAt A B a)

def CertifiedPartialTransformation.compose {A B C : Problem}
    (f : CertifiedPartialTransformation A B) (g : CertifiedPartialTransformation B C) :
    CertifiedPartialTransformation A C where
  forward := fun a => (f.forward a).bind fun first =>
    (g.forward first.input).map fun second => first.compose second

theorem partial_compose_some {A B C : Problem}
    (f : CertifiedPartialTransformation A B) (g : CertifiedPartialTransformation B C)
    (a : A.Input) (first : TransportAt A B a) (second : TransportAt B C first.input)
    (hf : f.forward a = some first) (hg : g.forward first.input = some second) :
    (f.compose g).forward a = some (first.compose second) := by
  simp [CertifiedPartialTransformation.compose, hf, hg]

theorem partial_compose_none {A B C : Problem}
    (f : CertifiedPartialTransformation A B) (g : CertifiedPartialTransformation B C)
    (a : A.Input) (hf : f.forward a = none) : (f.compose g).forward a = none := by
  simp [CertifiedPartialTransformation.compose, hf]

theorem partial_transport_sound {A B : Problem} {a : A.Input}
    (step : TransportAt A B a) (valid : A.Valid a) (r : B.Result step.input)
    (correct : B.Correct step.input r) : A.Correct a (step.extract r) :=
  step.sound valid r correct

structure OptimizationProblem extends Problem.{u, v} where
  cost : (a : Input) → Result a → Nat

def OptimizationProblem.Optimal (A : OptimizationProblem) (a : A.Input) (r : A.Result a) : Prop :=
  A.Correct a r ∧ ∀ s, A.Correct a s → A.cost a r ≤ A.cost a s

/-- Optimality transport is an additional law, separate from witness correctness. -/
structure CertifiedOptimizationReduction (A B : OptimizationProblem.{u, v}) where
  transport : CertifiedTransformation A.toProblem B.toProblem
  optimal : ∀ a, A.Valid a → ∀ r, B.Optimal (transport.forward a) r →
    A.Optimal a (transport.extract a r)

def CertifiedOptimizationReduction.compose {A B C : OptimizationProblem}
    (f : CertifiedOptimizationReduction A B) (g : CertifiedOptimizationReduction B C) :
    CertifiedOptimizationReduction A C where
  transport := LeanPoo.Functional.Transformation.compose f.transport g.transport
  optimal := fun a valid r optimum =>
    f.optimal a valid _ (g.optimal _ (f.transport.preserves a valid) r optimum)

theorem optimization_compose_optimal {A B C : OptimizationProblem}
    (f : CertifiedOptimizationReduction A B) (g : CertifiedOptimizationReduction B C)
    (a : A.Input) (valid : A.Valid a)
    (r : C.Result ((f.compose g).transport.forward a))
    (optimum : C.Optimal ((f.compose g).transport.forward a) r) :
    A.Optimal a ((f.compose g).transport.extract a r) := (f.compose g).optimal a valid r optimum

end LeanPoo.Functional.Transformation

#print axioms LeanPoo.Functional.Transformation.decision_compose_equivalent
#print axioms LeanPoo.Functional.Transformation.partial_compose_some
#print axioms LeanPoo.Functional.Transformation.partial_compose_none
#print axioms LeanPoo.Functional.Transformation.partial_transport_sound
#print axioms LeanPoo.Functional.Transformation.optimization_compose_optimal
