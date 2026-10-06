import LeanPoo.Functional.FiniteTransformation
import LeanPoo.Functional.Transformation
import LeanPoo.Proof.Transformation
open LeanPoo.Functional.Transformation

-- Result types bind the exact input: an unrelated target answer cannot typecheck.
def indexed : Problem where
  Input := Nat
  Result := Fin
  Valid := fun n => 0 < n
  Correct := fun _ _ => True

#check identity indexed
#check compose_sound
#check compose_forward_assoc
#check compose_extract_assoc
#check LeanPoo.Proof.Transformation.two_shift_source_answer
example (input : Nat) : (identity indexed).forward input = input := rfl
example (input : Nat) (result : Fin input) :
    (compose (identity indexed) (identity indexed)).extract input result = result := rfl
#print axioms compose_sound
#print axioms compose_extract_assoc

open LeanPoo.Functional.Transformation

def finiteSource : FiniteSpecification 2 2 := ⟨fun i r => i == r⟩
def finiteForward (i : Fin 2) : Fin 2 := i
def finiteExtract (_ : Fin 2) (r : Fin 2) : Fin 2 := r
#guard finiteCheck finiteSource finiteSource finiteForward finiteExtract
#guard !(finiteCheck finiteSource finiteSource finiteForward (fun _ _ => 0))
def finiteIdentity := certifyFinite finiteSource finiteSource finiteForward finiteExtract (by decide)
#print axioms finiteCheck_sound
