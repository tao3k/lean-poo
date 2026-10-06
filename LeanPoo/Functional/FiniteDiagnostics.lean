import LeanPoo.Functional.FiniteTransformation

/-! Finite admission with a constructive, proof-carrying refusal witness. -/
namespace LeanPoo.Functional.Transformation

/-- A target answer is correct, but its extracted source answer is not. -/
structure FiniteFailure (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m) where
  input : Fin n
  answer : Fin q
  target_correct : target.correct (forward input) answer = true
  source_incorrect : source.correct input (extract input answer) = false

/-- A refusal witness rules out the existing exhaustive Boolean admission. -/
theorem FiniteFailure.rejects (bad : FiniteFailure source target forward extract) :
    finiteCheck source target forward extract = false := by
  cases checked : finiteCheck source target forward extract with
  | false => rfl
  | true =>
    have sound := finiteCheck_sound source target forward extract checked
      bad.input bad.answer bad.target_correct
    rw [bad.source_incorrect] at sound
    cases sound

private def checkRows (items : List α) (test : α → Bool) :
    Except {item : α // item ∈ items ∧ test item = false}
      (PLift (∀ item ∈ items, test item = true)) :=
  match items with
  | [] => .ok ⟨by simp⟩
  | head :: tail =>
    if checked : test head = true then
      match checkRows tail test with
      | .error bad => .error ⟨bad.val, by simp only [List.mem_cons]; exact ⟨Or.inr bad.property.1, bad.property.2⟩⟩
      | .ok sound => .ok ⟨by
          intro item member
          rcases List.mem_cons.mp member with equal | member
          · subst item; exact checked
          · exact sound.down item member⟩
    else .error ⟨head, by simp only [List.mem_cons, true_or]; exact ⟨True.intro, by simpa using checked⟩⟩

private def inspectInputs (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m) (inputs : List (Fin n)) :
    Except (FiniteFailure source target forward extract)
      (PLift (∀ input ∈ inputs, ∀ answer, target.correct (forward input) answer = true →
        source.correct input (extract input answer) = true)) :=
  match inputs with
  | [] => .ok ⟨by simp⟩
  | head :: tail =>
    match checkRows (List.finRange q)
        (fun answer => !target.correct (forward head) answer || source.correct head (extract head answer)) with
    | .error bad => .error {
        input := head, answer := bad.val
        target_correct := by
          have failure := bad.property.2
          cases ht : target.correct (forward head) bad.val <;> simp_all
        source_incorrect := by
          have failure := bad.property.2
          cases hs : source.correct head (extract head bad.val) <;> simp_all }
    | .ok sound =>
      match inspectInputs source target forward extract tail with
      | .error bad => .error bad
      | .ok rest => .ok ⟨by
          intro input member answer correct
          rcases List.mem_cons.mp member with equal | member
          · subst input
            have result := sound.down answer (List.mem_finRange answer)
            simpa only [correct, Bool.not_true, Bool.false_or] using result
          · exact rest.down input member answer correct⟩

/-- Scan inputs/answers in ascending order; admit or return an actual failure.
    No existential choice, Cartesian-product table or repeated Boolean check. -/
def certifyFiniteOrFailure (source : FiniteSpecification n m) (target : FiniteSpecification p q)
    (forward : Fin n → Fin p) (extract : Fin n → Fin q → Fin m) :
    Except (FiniteFailure source target forward extract)
      (CertifiedTransformation source.problem target.problem) :=
  match inspectInputs source target forward extract (List.finRange n) with
  | .error bad => .error bad
  | .ok sound => .ok {
      forward := forward, extract := extract
      preserves := fun _ _ => True.intro
      sound := fun input _ answer correct => sound.down input (List.mem_finRange input) answer correct }

end LeanPoo.Functional.Transformation
