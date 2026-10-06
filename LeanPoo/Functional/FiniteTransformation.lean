import LeanPoo.Functional.Transformation

/-! Decidable exhaustive certification for total transport on finite domains. -/
namespace LeanPoo.Functional.Transformation

structure FiniteSpecification (inputs answers : Nat) where
  correct : Fin inputs → Fin answers → Bool

def FiniteSpecification.problem (spec : FiniteSpecification n m) : Problem where
  Input := Fin n
  Result := fun _ => Fin m
  Valid := fun _ => True
  Correct := fun input answer => spec.correct input answer = true

def finiteCheck (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m) : Bool :=
  (List.finRange n).all fun input => (List.finRange q).all fun answer =>
    !target.correct (forward input) answer || source.correct input (extract input answer)

theorem finiteCheck_sound (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m)
    (checked : finiteCheck source target forward extract = true) :
    ∀ input answer, target.correct (forward input) answer = true →
      source.correct input (extract input answer) = true := by
  intro input answer correct
  have inputCheck := (List.all_eq_true.mp checked) input (List.mem_finRange input)
  have answerCheck := (List.all_eq_true.mp inputCheck) answer (List.mem_finRange answer)
  simpa only [correct, Bool.not_true, Bool.false_or] using answerCheck

/-- Only an exhaustive successful check constructs a certified transformation. -/
def certifyFinite (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m)
    (checked : finiteCheck source target forward extract = true) :
    CertifiedTransformation source.problem target.problem where
  forward := forward
  preserves := fun _ _ => True.intro
  extract := extract
  sound := fun input _ answer correct => finiteCheck_sound source target forward extract checked input answer correct

end LeanPoo.Functional.Transformation
