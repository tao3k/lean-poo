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
  decide (∀ input answer, target.correct (forward input) answer = true →
    source.correct input (extract input answer) = true)

theorem finiteCheck_sound (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m)
    (checked : finiteCheck source target forward extract = true) :
    ∀ input answer, target.correct (forward input) answer = true →
      source.correct input (extract input answer) = true := by
  exact of_decide_eq_true checked

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
