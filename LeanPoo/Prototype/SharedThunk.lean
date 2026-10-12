import LeanPoo.Prototype.RecursiveCache
import LeanPoo.Prototype.Compose

/-! An executable bridge from the actual shared knot to the explicit recursive
calculus. Native execution supplies data, never a trusted proof. A total checker
reconstructs the derivation for the exact program and checks the reported result.
The private IO cell and native thunk implementation remain a runtime boundary. -/
namespace LeanPoo.Prototype.Recursive.Shared

open Cached

/-- A finite demand tree. A cut represents unfinished execution. Values and
errors are recovered from the current program, rather than trusted trace data. -/
inductive Trace where
  | cut
  | value
  | error
  | callValue (head tail : Trace)
  | callError (head : Trace)
  deriving Repr, BEq, DecidableEq

structure Candidate (α : Type) where
  result : Observation α
  trace : Trace
  deriving Repr, BEq

/-- Interpret local continuations using the recursive self supplied by the
shared closure. Trace construction does not invoke a second recursive solver. -/
def record (self : Input → Candidate Output) :
    Interaction Input Output α → Candidate α
  | .value answer => ⟨.value answer, .value⟩
  | .error message => ⟨.error message, .error⟩
  | .call input next =>
    let head := self input
    match head.result with
    | .pending => ⟨.pending, .cut⟩
    | .error message => ⟨.error message, .callError head.trace⟩
    | .value answer =>
      let tail := record self (next answer)
      ⟨tail.result, .callValue head.trace tail.trace⟩

theorem record_result (self : Input → Candidate Output)
    (tree : Interaction Input Output α) :
    (record self tree).result = tree.interpret (fun input => (self input).result) := by
  induction tree with
  | value => rfl
  | error => rfl
  | call input next ih =>
    simp only [record, Interaction.interpret]
    cases found : (self input).result with
    | pending => rfl
    | error => rfl
    | value answer => exact ih answer

/-- Source-depth bounded recording. A pending result is data, not a proof of
divergence. This definition also specifies the native bounded compiler. -/
def recordSolve (program : Generator Input Output) : Nat → Input → Candidate Output
  | 0, _ => ⟨.pending, .cut⟩
  | depth + 1, input => record (recordSolve program depth) (program input)

theorem recordSolve_result (program : Generator Input Output) (depth : Nat) (input : Input) :
    (recordSolve program depth input).result = solve program depth input := by
  induction depth generalizing input with
  | zero => rfl
  | succ depth ih =>
    simp only [recordSolve, solve, record_result]
    congr 1
    funext query
    exact ih query

/-- Replay only the finite demand tree. All values, errors and continuations
come from the exact current program. No unsafe declaration is used here. -/
def check (program : Generator Input Output) :
    (tree : Interaction Input Output α) → Trace → Option (Receipt program tree)
  | .value answer, .value => some ⟨.value answer, .value⟩
  | .error message, .error => some ⟨.error message, .error⟩
  | .call input next, .callValue head tail => do
    let headReceipt ← check program (program input) head
    match headReceipt with
    | ⟨.error _, _⟩ => none
    | ⟨.value answer, proof⟩ =>
      let tailReceipt ← check program (next answer) tail
      return ⟨tailReceipt.result, .callValue proof tailReceipt.sound⟩
  | .call input _, .callError head => do
    let headReceipt ← check program (program input) head
    match headReceipt with
    | ⟨.value _, _⟩ => none
    | ⟨.error message, proof⟩ => return ⟨.error message, .callError proof⟩
  | _, _ => none
termination_by _ trace => trace

/-- The shared closure's terminating operational executions, retaining the
actual recursive demand trace and error short circuit. -/
inductive Runs (program : Generator Input Output) :
    {α : Type} → Interaction Input Output α → Candidate α → Prop where
  | value : Runs program (.value answer) ⟨.value answer, .value⟩
  | error : Runs program (.error message) ⟨.error message, .error⟩
  | callValue (head : Runs program (program input) ⟨.value answer, headTrace⟩)
      (tail : Runs program (next answer) ⟨result, tailTrace⟩) :
      Runs program (.call input next) ⟨result, .callValue headTrace tailTrace⟩
  | callError (head : Runs program (program input) ⟨.error message, headTrace⟩) :
      Runs program (.call input next) ⟨.error message, .callError headTrace⟩

theorem Runs.evaluates (execution : Runs program tree candidate) :
    Evaluates program tree candidate.result := by
  induction execution with
  | value => exact .value
  | error => exact .error
  | callValue _ _ head tail => exact .callValue head tail
  | callError _ head => exact .callError head

theorem evaluation_trace (evaluation : Evaluates program tree result) :
    ∃ trace, Runs program tree ⟨result, trace⟩ := by
  induction evaluation with
  | value => exact ⟨.value, .value⟩
  | error => exact ⟨.error, .error⟩
  | callValue _ _ head tail =>
    obtain ⟨headTrace, head⟩ := head
    obtain ⟨tailTrace, tail⟩ := tail
    exact ⟨.callValue headTrace tailTrace, .callValue head tail⟩
  | callError _ head =>
    obtain ⟨headTrace, head⟩ := head
    exact ⟨.callError headTrace, .callError head⟩

theorem runs_iff_evaluates (program : Generator Input Output)
    (tree : Interaction Input Output α) (result : Observation α) :
    (∃ trace, Runs program tree ⟨result, trace⟩) ↔ Evaluates program tree result :=
  ⟨fun ⟨_, execution⟩ => execution.evaluates, evaluation_trace⟩

theorem Runs.checked (execution : Runs program tree candidate) :
    ∃ receipt, check program tree candidate.trace = some receipt ∧
      receipt.result.observation = candidate.result := by
  induction execution with
  | value => exact ⟨⟨.value _, .value⟩, by simp [check], rfl⟩
  | error => exact ⟨⟨.error _, .error⟩, by simp [check], rfl⟩
  | callValue head tail headIH tailIH =>
    obtain ⟨headReceipt, checkedHead, resultHead⟩ := headIH
    obtain ⟨tailReceipt, checkedTail, resultTail⟩ := tailIH
    cases headReceipt with
    | mk completed proof =>
      cases completed with
      | error => simp [Completed.observation] at resultHead
      | value answer =>
        simp only [Completed.observation, Observation.value.injEq] at resultHead
        subst answer
        exact ⟨⟨tailReceipt.result, .callValue proof tailReceipt.sound⟩,
          by simp [check, checkedHead, checkedTail], resultTail⟩
  | callError head headIH =>
    obtain ⟨headReceipt, checkedHead, resultHead⟩ := headIH
    cases headReceipt with
    | mk completed proof =>
      cases completed with
      | value => simp [Completed.observation] at resultHead
      | error message =>
        simp only [Completed.observation, Observation.error.injEq] at resultHead
        subst message
        exact ⟨⟨.error _, .callError proof⟩, by simp [check, checkedHead], rfl⟩

theorem check_runs (program : Generator Input Output) (trace : Trace)
    (tree : Interaction Input Output α) (receipt : Receipt program tree)
    (accepted : check program tree trace = some receipt) :
    Runs program tree ⟨receipt.result.observation, trace⟩ := by
  induction trace generalizing α with
  | cut => simp [check] at accepted
  | value =>
    cases tree <;> simp [check] at accepted
    case value answer => cases accepted; exact .value
  | error =>
    cases tree <;> simp [check] at accepted
    case error message => cases accepted; exact .error
  | callValue head tail headIH tailIH =>
    cases tree with
    | value => simp [check] at accepted
    | error => simp [check] at accepted
    | call input next =>
      cases headFound : check program (program input) head with
      | none => simp [check, headFound] at accepted
      | some headReceipt =>
        cases headReceipt with
        | mk completed proof =>
          cases completed with
          | error => simp [check, headFound] at accepted
          | value answer =>
            cases tailFound : check program (next answer) tail with
            | none => simp [check, headFound, tailFound] at accepted
            | some tailReceipt =>
              simp [check, headFound, tailFound] at accepted
              cases accepted
              exact .callValue (headIH _ _ headFound) (tailIH _ _ tailFound)
  | callError head headIH =>
    cases tree with
    | value => simp [check] at accepted
    | error => simp [check] at accepted
    | call input next =>
      cases headFound : check program (program input) head with
      | none => simp [check, headFound] at accepted
      | some headReceipt =>
        cases headReceipt with
        | mk completed proof =>
          cases completed with
          | value => simp [check, headFound] at accepted
          | error message =>
            simp [check, headFound] at accepted
            cases accepted
            exact .callError (headIH _ _ headFound)

/-- Admission compares the native reported result as well as checking the
demand trace. Forged values and errors cannot acquire an evaluation proof. -/
def admit [DecidableEq α] (program : Generator Input Output)
    (tree : Interaction Input Output α) (candidate : Candidate α) :
    Option (Receipt program tree) := do
  let receipt ← check program tree candidate.trace
  if receipt.result.observation = candidate.result then some receipt else none

theorem admit_iff_runs [DecidableEq α] (program : Generator Input Output)
    (tree : Interaction Input Output α) (candidate : Candidate α) :
    (∃ receipt, admit program tree candidate = some receipt) ↔ Runs program tree candidate := by
  constructor
  · rintro ⟨receipt, accepted⟩
    cases found : check program tree candidate.trace with
    | none => simp [admit, found] at accepted
    | some checked =>
      by_cases same : checked.result.observation = candidate.result
      · have execution := check_runs program candidate.trace tree checked found
        cases candidate with
        | mk result trace => simpa [same] using execution
      · simp [admit, found, same] at accepted
  · intro execution
    obtain ⟨receipt, checked, same⟩ := execution.checked
    exact ⟨receipt, by simp [admit, checked, same]⟩

theorem record_runs (program : Generator Input Output) (self : Input → Candidate Output)
    (sound : ∀ input, (self input).result ≠ .pending →
      Runs program (program input) (self input))
    (tree : Interaction Input Output α) (known : (record self tree).result ≠ .pending) :
    Runs program tree (record self tree) := by
  induction tree with
  | value => exact .value
  | error => exact .error
  | call input next ih =>
    cases found : self input with
    | mk result trace =>
      cases result with
      | pending => simp [record, found] at known
      | error message =>
        have head := sound input (by simp [found])
        simpa [record, found] using
          (Runs.callError (next := next) (by simpa [found] using head))
      | value answer =>
        have head := sound input (by simp [found])
        have tail := ih answer (by simpa [record, found] using known)
        cases tailFound : record self (next answer) with
        | mk tailResult tailTrace =>
          simpa [record, found, tailFound] using
            (Runs.callValue (by simpa [found] using head) (by simpa [tailFound] using tail))

theorem recordSolve_runs (program : Generator Input Output) (depth : Nat) (input : Input)
    (known : (recordSolve program depth input).result ≠ .pending) :
    Runs program (program input) (recordSolve program depth input) := by
  induction depth generalizing input with
  | zero => simp [recordSolve] at known
  | succ depth ih => exact record_runs program _ ih _ known

theorem recordSolve_admitted [DecidableEq Output] (program : Generator Input Output)
    (depth : Nat) (input : Input) (known : solve program depth input ≠ .pending) :
    ∃ receipt, admit program (program input) (recordSolve program depth input) = some receipt :=
  (admit_iff_runs _ _ _).mpr
    (recordSolve_runs program depth input (by rwa [recordSolve_result]))

/-- Both admitted native values and admitted native errors have a finite safe
observation. This theorem quantifies over untrusted candidate data. -/
theorem admitted_observed [DecidableEq Output] (program : Generator Input Output)
    (input : Input) (candidate : Candidate Output)
    (accepted : ∃ receipt, admit program (program input) candidate = some receipt) :
    ∃ depth, solve program depth input = candidate.result :=
  solve_complete ((admit_iff_runs _ _ _).mp accepted).evaluates

theorem admit_result [DecidableEq α] (program : Generator Input Output)
    (tree : Interaction Input Output α) (candidate : Candidate α)
    (receipt : Receipt program tree) (accepted : admit program tree candidate = some receipt) :
    receipt.result.observation = candidate.result := by
  cases found : check program tree candidate.trace with
  | none => simp [admit, found] at accepted
  | some checked =>
    by_cases same : checked.result.observation = candidate.result
    · simp [admit, found, same] at accepted
      cases accepted
      exact same
    · simp [admit, found, same] at accepted

theorem evaluation_admitted [DecidableEq Output] (program : Generator Input Output)
    (input : Input) (result : Observation Output)
    (evaluation : Evaluates program (program input) result) :
    ∃ depth receipt, (recordSolve program depth input).result = result ∧
      admit program (program input) (recordSolve program depth input) = some receipt := by
  obtain ⟨depth, observed⟩ := solve_complete evaluation
  obtain ⟨receipt, accepted⟩ := recordSolve_admitted program depth input
    (by rw [observed]; exact evaluation.known)
  exact ⟨depth, receipt, (recordSolve_result _ _ _).trans observed, accepted⟩

theorem diverges_iff_no_runs (program : Generator Input Output) (input : Input) :
    Diverges program input ↔ ∀ candidate, ¬Runs program (program input) candidate := by
  rw [diverges_iff_no_evaluation]
  constructor
  · intro absent candidate execution
    exact absent _ execution.evaluates
  · intro absent result evaluation
    obtain ⟨trace, execution⟩ := evaluation_trace evaluation
    exact absent ⟨result, trace⟩ execution

/-- Actual unbounded native execution: one existing `instantiate`/`sharedFix`
closure, and recursive requests through its final-self handle. May diverge. -/
unsafe def compile (program : Generator Input Output) :
    FixedFunction Input (Candidate Output) :=
  LeanPoo.Prototype.instantiate
    (fun self (_ : Unit) => FixedFunction.ofFun fun input =>
      record (fun query => self query) (program input)) ()

/-- Actual shared execution bounded by recursive source depth. The function
wrapper prevents eta expansion from rebuilding the tied closure at each call. -/
unsafe def compileBounded (program : Generator Input Output) :
    FixedFunction (Nat × Input) (Candidate Output) :=
  LeanPoo.Prototype.instantiate
    (fun self (_ : Unit) => FixedFunction.ofFun fun (depth, input) =>
      match depth with
      | 0 => ⟨.pending, .cut⟩
      | depth + 1 => record (fun query => self (depth, query)) (program input)) ()

/-- Delayed non-function values use the existing shared constructor directly. -/
unsafe def compileValue (tree : Interaction Unit α α) : Thunk (Candidate α) :=
  sharedFix fun self => record (fun _ => self.get) tree

/-- A native executor supplies untrusted candidate data at the safe interface.
A substituted executor must also pass current-program admission. -/
structure Runtime (program : Generator Input Output) where
  executor : FixedFunction Input (Candidate Output)

unsafe def Runtime.new (program : Generator Input Output) : Runtime program := ⟨compile program⟩

unsafe def Runtime.bounded (program : Generator Input Output) (depth : Nat) : Runtime program :=
  let native := compileBounded program
  ⟨FixedFunction.ofFun fun input => native (depth, input)⟩

inductive ReadError where
  | unfinished
  | invalidTrace
  deriving Repr, BEq, DecidableEq

/-- Safe admission of the native executor's actual answer. Completed source
errors remain receipts; unfinished and invalid executions are diagnostics. -/
def Runtime.read [DecidableEq Output] {program : Generator Input Output}
    (runtime : Runtime program) (input : Input) :
    Except ReadError (Receipt program (program input)) :=
  let candidate := runtime.executor input
  match candidate.result with
  | .pending => .error .unfinished
  | _ => match admit program (program input) candidate with
    | none => .error .invalidTrace
    | some receipt => .ok receipt

theorem Runtime.read_matches [DecidableEq Output] {program : Generator Input Output}
    (runtime : Runtime program) (input : Input)
    (receipt : Receipt program (program input)) (accepted : runtime.read input = .ok receipt) :
    receipt.result.observation = (runtime.executor input).result := by
  unfold Runtime.read at accepted
  cases found : (runtime.executor input).result with
  | pending => simp [found] at accepted
  | error message =>
    cases admitted : admit program (program input) (runtime.executor input) with
    | none => simp [found, admitted] at accepted
    | some checked =>
      simp [found, admitted] at accepted
      cases accepted
      simpa [found] using admit_result _ _ _ _ admitted
  | value answer =>
    cases admitted : admit program (program input) (runtime.executor input) with
    | none => simp [found, admitted] at accepted
    | some checked =>
      simp [found, admitted] at accepted
      cases accepted
      simpa [found] using admit_result _ _ _ _ admitted

theorem Runtime.read_observed [DecidableEq Output] {program : Generator Input Output}
    (runtime : Runtime program) (input : Input)
    (receipt : Receipt program (program input)) (accepted : runtime.read input = .ok receipt) :
    ∃ depth, solve program depth input = (runtime.executor input).result := by
  obtain ⟨depth, observed⟩ := receipt.observed
  exact ⟨depth, observed.trans (runtime.read_matches input receipt accepted)⟩

end LeanPoo.Prototype.Recursive.Shared
