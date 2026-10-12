import LeanPoo.Prototype.Recursive

/-! Unbounded operational meaning and source/target transfer for `fix`/`mix`.
No finite budget exhaustion is identified with divergence. -/
namespace LeanPoo.Prototype.Recursive

/-- Finite terminating derivations of an unrestricted recursive computation. -/
inductive Evaluates (program : Generator Input Output) :
    {α : Type} → Interaction Input Output α → Observation α → Prop where
  | value : Evaluates program (.value result) (.value result)
  | error : Evaluates program (.error message) (.error message)
  | callValue (head : Evaluates program (program input) (.value answer))
      (tail : Evaluates program (next answer) result) :
      Evaluates program (.call input next) result
  | callError (head : Evaluates program (program input) (.error message)) :
      Evaluates program (.call input next) (.error message)

theorem Evaluates.known (evaluation : Evaluates program tree result) :
    result ≠ .pending := by
  induction evaluation with
  | value => simp
  | error => simp
  | callValue _ _ _ ih => exact ih
  | callError => simp

private theorem interpret_sound (program : Generator Input Output)
    (oracle : Input → Observation Output)
    (sound : ∀ input result, oracle input = result → result ≠ .pending →
      Evaluates program (program input) result)
    (tree : Interaction Input Output α) (result : Observation α)
    (success : tree.interpret oracle = result) (known : result ≠ .pending) :
    Evaluates program tree result := by
  induction tree generalizing result with
  | value answer => cases success; exact .value
  | error message => cases success; exact .error
  | call input next ih =>
    simp only [Interaction.interpret] at success
    cases found : oracle input with
    | pending => simp [found] at success; exact False.elim (known success.symm)
    | error message =>
      simp only [found] at success
      cases success
      exact .callError (sound input _ found (by simp))
    | value answer =>
      simp only [found] at success
      exact .callValue (sound input _ found (by simp)) (ih answer result success known)

/-- Every completed executable observation has an unbounded operational proof. -/
theorem solve_sound (program : Generator Input Output) (depth : Nat) (input : Input)
    (result : Observation Output) (success : solve program depth input = result)
    (known : result ≠ .pending) : Evaluates program (program input) result := by
  induction depth generalizing input result with
  | zero => exact False.elim (known success.symm)
  | succ depth ih =>
    exact interpret_sound program (solve program depth)
      (fun input result success known => ih input result success known)
      (program input) result success known

/-- Every unbounded operational proof is observed at some finite depth. -/
theorem Evaluates.complete (evaluation : Evaluates program tree result) :
    ∃ depth, tree.interpret (solve program depth) = result := by
  induction evaluation with
  | value => exact ⟨0, rfl⟩
  | error => exact ⟨0, rfl⟩
  | @callValue input answer _ next result head tail headIH tailIH =>
    obtain ⟨n, hn⟩ := headIH
    obtain ⟨m, hm⟩ := tailIH
    have headAt : solve program (n + 1) input = .value answer := hn
    let depth := max (n + 1) m
    have headGrows := solve_refines program (n + 1) depth (Nat.le_max_left _ _) input
    have headDone : solve program depth input = .value answer := by
      have same := headGrows.known (by simp [headAt])
      exact same.symm.trans headAt
    have tailGrows := Interaction.interpret_refines (solve program m) (solve program depth)
      (fun query => solve_refines program m depth (Nat.le_max_right _ _) query) (next answer)
    have tailDone : (next answer).interpret (solve program depth) = result := by
      exact (tailGrows.known (by rw [hm]; exact tail.known)).symm.trans hm
    exact ⟨depth, by simp [Interaction.interpret, headDone, tailDone]⟩
  | @callError input message _ next head ih =>
    obtain ⟨n, hn⟩ := ih
    have headAt : solve program (n + 1) input = .error message := hn
    exact ⟨n + 1, by simp [Interaction.interpret, headAt]⟩

theorem solve_complete (evaluation : Evaluates program (program input) result) :
    ∃ depth, solve program depth input = result := by
  obtain ⟨depth, success⟩ := evaluation.complete
  exact ⟨depth + 1, success⟩

theorem returns_iff_evaluates (program : Generator Input Output) (input : Input) (result : Output) :
    Returns program input result ↔ Evaluates program (program input) (.value result) := by
  constructor
  · rintro ⟨depth, success⟩
    exact solve_sound program depth input _ success (by simp)
  · exact solve_complete

theorem fails_iff_evaluates (program : Generator Input Output) (input : Input) (message : String) :
    Fails program input message ↔ Evaluates program (program input) (.error message) := by
  constructor
  · rintro ⟨depth, success⟩
    exact solve_sound program depth input _ success (by simp)
  · exact solve_complete

/-- Divergence is precisely the absence of a completed operational derivation. -/
theorem diverges_iff_no_evaluation (program : Generator Input Output) (input : Input) :
    Diverges program input ↔ ∀ result, ¬Evaluates program (program input) result := by
  constructor
  · intro divergent result evaluation
    obtain ⟨depth, success⟩ := solve_complete evaluation
    exact evaluation.known (success.symm.trans (divergent depth))
  · intro absent depth
    cases found : solve program depth input with
    | pending => rfl
    | error message => exact False.elim (absent _ (solve_sound _ _ _ _ found (by simp)))
    | value answer => exact False.elim (absent _ (solve_sound _ _ _ _ found (by simp)))

inductive Observation.Rel (values : α → β → Prop) : Observation α → Observation β → Prop where
  | pending : Rel values .pending .pending
  | error : Rel values (.error message) (.error message)
  | value (related : values left right) : Rel values (.value left) (.value right)

theorem Observation.Rel.pending_iff (related : Rel values left right) :
    left = .pending ↔ right = .pending := by cases related <;> simp

theorem Observation.Rel.error_right (related : Rel values left right)
    (failed : left = .error message) : right = .error message := by
  cases related <;> simp_all

theorem Observation.Rel.value_right (related : Rel values left right)
    (returned : left = .value result) : ∃ result', right = .value result' ∧ values result result' := by
  cases related <;> simp_all

/-- A compiler relation may change both request and answer carriers. Errors
must agree and each recursive answer must preserve the continuation relation. -/
inductive Interaction.Rel (inputs : Input → Input' → Prop) (answers : Output → Output' → Prop)
    (values : α → β → Prop) : Interaction Input Output α → Interaction Input' Output' β → Prop where
  | value (related : values left right) : Rel inputs answers values (.value left) (.value right)
  | error : Rel inputs answers values (.error message) (.error message)
  | call (related : inputs left right)
      (next : ∀ answer answer', answers answer answer' →
        Rel inputs answers values (leftNext answer) (rightNext answer')) :
      Rel inputs answers values (.call left leftNext) (.call right rightNext)

theorem Interaction.interpret_relation
    (leftOracle : Input → Observation Output) (rightOracle : Input' → Observation Output')
    (inputs : Input → Input' → Prop) (answers : Output → Output' → Prop) (values : α → β → Prop)
    (oracleRelated : ∀ input input', inputs input input' →
      Observation.Rel answers (leftOracle input) (rightOracle input'))
    (left : Interaction Input Output α) (right : Interaction Input' Output' β)
    (related : Interaction.Rel inputs answers values left right) :
    Observation.Rel values (left.interpret leftOracle) (right.interpret rightOracle) := by
  induction left generalizing right with
  | value result => cases related with | value relation => exact .value relation
  | error message => cases related; exact .error
  | call input next ih =>
    cases related with
    | @call _ other _ rightNext inputsRelated continuations =>
      have oracle := oracleRelated input other inputsRelated
      cases found : leftOracle input with
      | pending =>
        have targetPending := oracle.pending_iff.mp found
        simp only [Interaction.interpret, found, targetPending]
        exact .pending
      | error message =>
        have targetError := oracle.error_right found
        simp only [Interaction.interpret, found, targetError]
        exact .error
      | value answer =>
        obtain ⟨answer', targetAnswer, answersRelated⟩ := oracle.value_right found
        simp only [Interaction.interpret, found, targetAnswer]
        exact ih _ _ (continuations _ _ answersRelated)

/-- Whole recursive observations transfer at every depth; this includes
all terminating/error derivations and divergence through the theorems above. -/
theorem solve_relation (source : Generator Input Output) (target : Generator Input' Output')
    (inputs : Input → Input' → Prop) (outputs : Output → Output' → Prop)
    (programRelated : ∀ input input', inputs input input' →
      Interaction.Rel inputs outputs outputs (source input) (target input'))
    (depth : Nat) (input : Input) (input' : Input') (related : inputs input input') :
    Observation.Rel outputs (solve source depth input) (solve target depth input') := by
  induction depth generalizing input input' with
  | zero => exact .pending
  | succ depth ih =>
    exact Interaction.interpret_relation _ _ inputs outputs outputs ih _ _
      (programRelated _ _ related)

theorem divergence_relation (source : Generator Input Output) (target : Generator Input' Output')
    (inputs : Input → Input' → Prop) (outputs : Output → Output' → Prop)
    (programRelated : ∀ input input', inputs input input' →
      Interaction.Rel inputs outputs outputs (source input) (target input'))
    (input : Input) (input' : Input') (related : inputs input input') :
    Diverges source input ↔ Diverges target input' := by
  constructor <;> intro divergent depth
  · have both := solve_relation source target inputs outputs programRelated depth input input' related
    exact both.pending_iff.mp (divergent depth)
  · have both := solve_relation source target inputs outputs programRelated depth input input' related
    exact both.pending_iff.mpr (divergent depth)

theorem returns_relation (source : Generator Input Output) (target : Generator Input' Output')
    (inputs : Input → Input' → Prop) (outputs : Output → Output' → Prop)
    (programRelated : ∀ input input', inputs input input' →
      Interaction.Rel inputs outputs outputs (source input) (target input'))
    (input : Input) (input' : Input') (related : inputs input input')
    (returned : Returns source input result) :
    ∃ result', outputs result result' ∧ Returns target input' result' := by
  obtain ⟨depth, success⟩ := returned
  have both := solve_relation source target inputs outputs programRelated depth input input' related
  obtain ⟨result', targetSuccess, outputRelated⟩ := both.value_right success
  exact ⟨result', outputRelated, depth, targetSuccess⟩

theorem fails_relation (source : Generator Input Output) (target : Generator Input' Output')
    (inputs : Input → Input' → Prop) (outputs : Output → Output' → Prop)
    (programRelated : ∀ input input', inputs input input' →
      Interaction.Rel inputs outputs outputs (source input) (target input'))
    (input : Input) (input' : Input') (related : inputs input input')
    (failed : Fails source input message) : Fails target input' message := by
  obtain ⟨depth, success⟩ := failed
  exact ⟨depth, (solve_relation source target inputs outputs programRelated depth input input' related)
    |>.error_right success⟩

/-- Any actual fixed point of the operational generator contains every finite
observation. This establishes the least-information part of `fix`. -/
theorem solve_le_fixed (program : Generator Input Output) (fixed : Input → Observation Output)
    (equation : ∀ input, (program input).interpret fixed = fixed input)
    (depth : Nat) (input : Input) : (solve program depth input).Refines (fixed input) := by
  induction depth generalizing input with
  | zero => exact Or.inl rfl
  | succ depth ih =>
    rw [solve_succ, ← equation input]
    exact Interaction.interpret_refines _ _ ih _

end LeanPoo.Prototype.Recursive
