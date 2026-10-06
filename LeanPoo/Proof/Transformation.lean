import LeanPoo.Functional.Transformation

namespace LeanPoo.Proof.Transformation
open LeanPoo.Functional.Transformation


-- Nontrivial concrete correctness: the answer must equal the original input.
abbrev naturalAnswer : Problem where
  Input := Nat
  Result := fun _ => Nat
  Valid := fun _ => True
  Correct := fun input answer => answer = input

def shift (amount : Nat) : CertifiedTransformation naturalAnswer naturalAnswer where
  forward := fun input => input + amount
  preserves := fun _ _ => True.intro
  extract := fun _ answer => answer - amount
  sound := by
    intro input _ answer correct
    change answer = input + amount at correct
    change answer - amount = input
    exact (congrArg (fun value => value - amount) correct).trans
      (Nat.add_sub_cancel input amount)

theorem two_shift_source_answer (input : Nat) :
    (compose (shift 1) (shift 2)).extract input
      ((compose (shift 1) (shift 2)).forward input) = input :=
  compose_sound (shift 1) (shift 2) input True.intro _ rfl

theorem incorrect_extractor_rejected : (7 : Nat) ≠ 5 := by decide

-- The finite oracle checks actual forward/solver/reverse extraction, not IDs.
#guard (List.range 32).all (fun input =>
  let route := compose (shift 1) (shift 2)
  route.extract input (route.forward input) == input)
#guard !((List.range 32).all (fun input => input + 3 == input))

#print axioms two_shift_source_answer
#print axioms incorrect_extractor_rejected

end LeanPoo.Proof.Transformation
