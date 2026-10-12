import LeanPoo.Prototype.RecursiveSemantics

/-! Change the request carrier without changing recursive observations. This
lets value-only records enter the parameterized method protocol, using one
distinguished argument for their existing final-self field requests. -/
namespace LeanPoo.Prototype.Recursive

def Interaction.relabel (rename : Input → Other)
    (tree : Interaction Input Output α) : Interaction Other Output α :=
  match tree with
  | .value result => .value result
  | .error message => .error message
  | .call input next => .call (rename input) (fun value => (next value).relabel rename)

theorem Interaction.interpret_relabel (rename : Input → Other)
    (tree : Interaction Input Output α) (oldOracle : Input → Observation Output)
    (newOracle : Other → Observation Output)
    (agrees : ∀ input, newOracle (rename input) = oldOracle input) :
    (tree.relabel rename).interpret newOracle = tree.interpret oldOracle := by
  induction tree with
  | value => rfl
  | error => rfl
  | call input next ih =>
    simp only [Interaction.relabel, Interaction.interpret, agrees]
    cases oldOracle input with
    | pending => rfl
    | error => rfl
    | value result => exact ih result

def Generator.reindex (program : Generator Input Output) (project : Other → Input)
    (embed : Input → Other) : Generator Other Output :=
  fun input => (program (project input)).relabel embed

theorem solve_reindex (program : Generator Input Output) (project : Other → Input)
    (embed : Input → Other) (retract : ∀ input, project (embed input) = input)
    (depth : Nat) (input : Other) :
    solve (program.reindex project embed) depth input = solve program depth (project input) := by
  induction depth generalizing input with
  | zero => rfl
  | succ depth ih =>
    simp only [solve, Generator.reindex]
    apply Interaction.interpret_relabel
    intro query
    rw [ih, retract]

theorem evaluates_reindex (program : Generator Input Output) (project : Other → Input)
    (embed : Input → Other) (retract : ∀ input, project (embed input) = input)
    (input : Other) (result : Observation Output) :
    Evaluates (program.reindex project embed) ((program.reindex project embed) input) result ↔
      Evaluates program (program (project input)) result := by
  constructor
  · intro evaluation
    obtain ⟨depth, found⟩ := solve_complete evaluation
    rw [solve_reindex program project embed retract] at found
    exact solve_sound program depth (project input) result found evaluation.known
  · intro evaluation
    obtain ⟨depth, found⟩ := solve_complete evaluation
    apply solve_sound (program.reindex project embed) depth input result
    · rw [solve_reindex program project embed retract, found]
    · exact evaluation.known

end LeanPoo.Prototype.Recursive
