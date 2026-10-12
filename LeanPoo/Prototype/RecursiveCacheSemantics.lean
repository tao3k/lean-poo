import LeanPoo.Prototype.RecursiveCache

/-! Completeness of the shared evaluator and semantic meaning of its cycle
diagnostics. Budgets bound execution; they are not a divergence decision. -/
namespace LeanPoo.Prototype.Recursive.Cached

private def Stable : Except (Diagnostic Input) α → Prop
  | .error .budgetExhausted => False
  | _ => True

private theorem machine_monotone [DecidableEq Input]
    (program : Generator Input Output) (lower : Nat) :
    (∀ {α : Type} (tree : Interaction Input Output α) active cache upper result,
      lower ≤ upper → Stable result → evaluate program tree active cache lower = result →
      evaluate program tree active cache upper = result) ∧
    (∀ input active cache upper result,
      lower ≤ upper → Stable result → resolve program input active cache lower = result →
      resolve program input active cache upper = result) := by
  induction lower with
  | zero =>
    constructor
    · intro α tree active cache upper result bound stable found
      change Except.error Diagnostic.budgetExhausted = result at found
      rw [← found] at stable
      exact False.elim stable
    · intro input active cache upper result bound stable found
      change Except.error Diagnostic.budgetExhausted = result at found
      rw [← found] at stable
      exact False.elim stable
  | succ lower ih =>
    constructor
    · intro α tree active cache upper result bound stable found
      cases upper with
      | zero => omega
      | succ upper =>
        have bound' : lower ≤ upper := by omega
        cases tree with
        | value value => simpa [evaluate] using found
        | error message => simpa [evaluate] using found
        | call input next =>
          let updated : Cache program := { cache with statistics :=
            { cache.statistics with steps := cache.statistics.steps + 1 } }
          cases head : resolve program input active updated lower with
          | error diagnostic =>
            have headStable : Stable (.error diagnostic : Except (Diagnostic Input)
                (Receipt program (program input) × Cache program)) := by
              cases diagnostic with
              | budgetExhausted =>
                simp [evaluate, updated, head, bind, Except.bind] at found
                cases found
                exact stable
              | cycle => trivial
            have head' := ih.2 input active updated upper _ bound' headStable head
            simpa [evaluate, updated, head, head', bind, Except.bind] using found
          | ok pair =>
            rcases pair with ⟨receipt, cache'⟩
            have head' := ih.2 input active updated upper _ bound' (by trivial) head
            cases receipt with
            | mk completed proof =>
              cases completed with
              | error message =>
                simpa [evaluate, updated, head, head', bind, Except.bind] using found
              | value answer =>
                cases tail : evaluate program (next answer) active cache' lower with
                | error diagnostic =>
                  have tailStable : Stable (.error diagnostic : Except (Diagnostic Input)
                      (Receipt program (next answer) × Cache program)) := by
                    cases diagnostic with
                    | budgetExhausted =>
                      simp [evaluate, updated, head, tail, bind, Except.bind] at found
                      cases found
                      exact stable
                    | cycle => trivial
                  have tail' := ih.1 (next answer) active cache' upper _ bound' tailStable tail
                  simpa [evaluate, updated, head, head', tail, tail', bind, Except.bind] using found
                | ok pair =>
                  have tail' := ih.1 (next answer) active cache' upper _ bound' (by trivial) tail
                  simpa [evaluate, updated, head, head', tail, tail', bind, Except.bind] using found
    · intro input active cache upper result bound stable found
      cases upper with
      | zero => omega
      | succ upper =>
        have bound' : lower ≤ upper := by omega
        cases cached : cache.lookup input with
        | some receipt => simpa [resolve, cached] using found
        | none =>
          by_cases cycle : input ∈ active
          · simpa [resolve, cached, cycle] using found
          · let updated : Cache program := { cache with statistics :=
              { cache.statistics with misses := cache.statistics.misses + 1 } }
            cases body : evaluate program (program input) (input :: active) updated lower with
            | error diagnostic =>
              have bodyStable : Stable (.error diagnostic : Except (Diagnostic Input)
                  (Receipt program (program input) × Cache program)) := by
                cases diagnostic with
                | budgetExhausted =>
                  simp [resolve, cached, cycle, updated, body, bind, Except.bind] at found
                  cases found
                  exact stable
                | cycle => trivial
              have body' := ih.1 (program input) (input :: active) updated upper _ bound' bodyStable body
              simpa [resolve, cached, cycle, updated, body, body', bind, Except.bind] using found
            | ok pair =>
              have body' := ih.1 (program input) (input :: active) updated upper _ bound' (by trivial) body
              simpa [resolve, cached, cycle, updated, body, body', bind, Except.bind] using found

theorem evaluate_success_mono [DecidableEq Input] (program : Generator Input Output)
    (tree : Interaction Input Output α) active cache lower upper result
    (bound : lower ≤ upper) (success : evaluate program tree active cache lower = .ok result) :
    evaluate program tree active cache upper = .ok result :=
  (machine_monotone program lower).1 tree active cache upper _ bound (by trivial) success

theorem resolve_success_mono [DecidableEq Input] (program : Generator Input Output)
    input active cache lower upper result (bound : lower ≤ upper)
    (success : resolve program input active cache lower = .ok result) :
    resolve program input active cache upper = .ok result :=
  (machine_monotone program lower).2 input active cache upper _ bound (by trivial) success

theorem run_cycle_mono [DecidableEq Input] (program : Generator Input Output)
    input cache lower upper path (bound : lower ≤ upper)
    (cycle : run program input lower cache = .error (.cycle path)) :
    run program input upper cache = .error (.cycle path) :=
  (machine_monotone program lower).2 input [] cache upper _ bound (by trivial) cycle

private def Blocked (program : Generator Input Output) (active : List Input) (depth : Nat) : Prop :=
  ∀ input ∈ active, solve program depth input = .pending

private theorem Blocked.lower {lower : Nat} (blocked : Blocked program active upper) (bound : lower ≤ upper) :
    Blocked program active lower := by
  intro input member
  rcases solve_refines program lower upper bound input with pending | same
  · exact pending
  · exact same.trans (blocked input member)

private def Done [DecidableEq Input] (program : Generator Input Output)
    (tree : Interaction Input Output α) (active : List Input) (cache : Cache program)
    (result : Observation α) : Prop :=
  ∃ budget receipt next,
    evaluate program tree active cache budget = .ok (receipt, next) ∧
      receipt.result.observation = result

private def Resolved [DecidableEq Input] (program : Generator Input Output)
    (input : Input) (active : List Input) (cache : Cache program) (result : Observation Output) : Prop :=
  ∃ budget receipt next,
    resolve program input active cache budget = .ok (receipt, next) ∧
      receipt.result.observation = result

private theorem evaluate_complete_from_resolve [DecidableEq Input]
    (program : Generator Input Output) (depth : Nat) (active : List Input)
    (heads : ∀ input cache result, solve program depth input = result → result ≠ .pending →
      Resolved program input active cache result)
    (tree : Interaction Input Output α) cache result
    (observed : tree.interpret (solve program depth) = result) (known : result ≠ .pending) :
    Done program tree active cache result := by
  induction tree generalizing cache result with
  | value value =>
    cases observed
    exact ⟨1, ⟨.value value, .value⟩, _, rfl, rfl⟩
  | error message =>
    cases observed
    exact ⟨1, ⟨.error message, .error⟩, _, rfl, rfl⟩
  | call input next ih =>
    let updated : Cache program := { cache with statistics :=
      { cache.statistics with steps := cache.statistics.steps + 1 } }
    cases head : solve program depth input with
    | pending =>
      simp [Interaction.interpret, head] at observed
      exact False.elim (known observed.symm)
    | error message =>
      simp only [Interaction.interpret, head] at observed
      cases observed
      obtain ⟨budget, receipt, nextCache, success, same⟩ := heads input updated _ head (by simp)
      cases receipt with
      | mk completed proof =>
        cases completed with
        | value => simp [Completed.observation] at same
        | error message' =>
          simp only [Completed.observation, Observation.error.injEq] at same
          subst message'
          refine ⟨budget + 1, ⟨.error message, .callError proof⟩, nextCache, ?_, rfl⟩
          simp [evaluate, updated, success, bind, Except.bind, pure, Except.pure]
    | value answer =>
      simp only [Interaction.interpret, head] at observed
      obtain ⟨headBudget, receipt, headCache, headSuccess, same⟩ :=
        heads input updated _ head (by simp)
      cases receipt with
      | mk completed proof =>
        cases completed with
        | error => simp [Completed.observation] at same
        | value answer' =>
          simp only [Completed.observation, Observation.value.injEq] at same
          subst answer'
          obtain ⟨tailBudget, tailReceipt, tailCache, tailSuccess, tailSame⟩ :=
            ih answer headCache result observed known
          let budget := max headBudget tailBudget
          have headAt := resolve_success_mono program input active updated headBudget budget _
            (Nat.le_max_left _ _) headSuccess
          have tailAt := evaluate_success_mono program (next answer) active headCache tailBudget budget _
            (Nat.le_max_right _ _) tailSuccess
          refine ⟨budget + 1, ⟨tailReceipt.result, .callValue proof tailReceipt.sound⟩,
            tailCache, ?_, tailSame⟩
          simp [evaluate, updated, headAt, tailAt, bind, Except.bind, pure, Except.pure]

private theorem source_depth_complete [DecidableEq Input]
    (program : Generator Input Output) (depth : Nat) :
    (∀ input active cache result, Blocked program active depth →
      solve program depth input = result → result ≠ .pending →
      Resolved program input active cache result) ∧
    (∀ {α : Type} (tree : Interaction Input Output α) active cache result,
      Blocked program active depth → tree.interpret (solve program depth) = result →
      result ≠ .pending → Done program tree active cache result) := by
  induction depth with
  | zero =>
    have heads : ∀ input active cache result, Blocked program active 0 →
        solve program 0 input = result → result ≠ .pending →
        Resolved program input active cache result := by
      intro input active cache result blocked found known
      exact False.elim (known found.symm)
    exact ⟨heads, fun tree active cache result blocked found known =>
      evaluate_complete_from_resolve program 0 active
        (fun input cache result found known => heads input active cache result blocked found known)
        tree cache result found known⟩
  | succ depth ih =>
    have heads : ∀ input active cache result, Blocked program active (depth + 1) →
        solve program (depth + 1) input = result → result ≠ .pending →
        Resolved program input active cache result := by
      intro input active cache result blocked found known
      by_cases previous : solve program depth input = .pending
      · cases cached : cache.lookup input with
        | some receipt =>
          refine ⟨1, receipt, { cache with statistics :=
            { cache.statistics with hits := cache.statistics.hits + 1 } }, ?_, ?_⟩
          · simp [resolve, cached]
          · exact (receipt.agrees (depth + 1) (by rw [found]; exact known)).symm.trans found
        | none =>
          have absent : input ∉ active := by
            intro member
            exact known (found.symm.trans (blocked input member))
          have blocked' : Blocked program (input :: active) depth := by
            intro query member
            rcases List.mem_cons.mp member with same | member
            · subst query; exact previous
            · exact blocked.lower (by omega) query member
          let updated : Cache program := { cache with statistics :=
            { cache.statistics with misses := cache.statistics.misses + 1 } }
          obtain ⟨budget, receipt, next, success, same⟩ :=
            ih.2 (program input) (input :: active) updated result blocked' found known
          refine ⟨budget + 1, receipt,
            { next with entries := ⟨input, receipt⟩ :: next.entries }, ?_, same⟩
          simp [resolve, cached, absent, updated, success, bind, Except.bind, pure, Except.pure]
      · have earlier : solve program depth input = result :=
          ((solve_step_refines program depth input).known previous).trans found
        exact ih.1 input active cache result (blocked.lower (by omega)) earlier known
    exact ⟨heads, fun tree active cache result blocked found known =>
      evaluate_complete_from_resolve program (depth + 1) active
        (fun input cache result found known => heads input active cache result blocked found known)
        tree cache result found known⟩

/-- Every terminating or failing source computation completes with enough
machine budget, from any proof-bearing cache of this exact program. -/
theorem run_complete [DecidableEq Input] (program : Generator Input Output)
    (input : Input) (cache : Cache program) (result : Observation Output)
    (evaluation : Evaluates program (program input) result) :
    ∃ budget receipt next, run program input budget cache = .ok (receipt, next) ∧
      receipt.result.observation = result := by
  obtain ⟨depth, found⟩ := solve_complete evaluation
  exact (source_depth_complete program depth).1 input [] cache result
    (by intro query member; cases member) found evaluation.known

/-- Reported active cycles are actual semantic divergence, rather than source
errors. This conclusion depends on completeness and stable cycle diagnostics. -/
theorem run_cycle_diverges [DecidableEq Input] (program : Generator Input Output)
    input budget cache path (cycle : run program input budget cache = .error (.cycle path)) :
    Diverges program input := by
  apply (diverges_iff_no_evaluation program input).mpr
  intro result evaluation
  obtain ⟨other, receipt, next, completed, same⟩ := run_complete program input cache result evaluation
  have completed' := resolve_success_mono program input [] cache other (max budget other) _
    (Nat.le_max_right _ _) completed
  have cycle' := run_cycle_mono program input cache budget (max budget other) path
    (Nat.le_max_left _ _) cycle
  simp only [run] at cycle'
  rw [cycle'] at completed'
  contradiction

theorem run_iff_evaluates [DecidableEq Input] (program : Generator Input Output)
    (input : Input) (cache : Cache program) (result : Observation Output) :
    (∃ budget receipt next, run program input budget cache = .ok (receipt, next) ∧
      receipt.result.observation = result) ↔ Evaluates program (program input) result := by
  constructor
  · rintro ⟨budget, receipt, next, completed, same⟩
    exact same ▸ receipt.sound
  · exact run_complete program input cache result

theorem diverges_iff_no_run [DecidableEq Input] (program : Generator Input Output)
    (input : Input) (cache : Cache program) :
    Diverges program input ↔
      ∀ budget receipt next, run program input budget cache ≠ .ok (receipt, next) := by
  constructor
  · intro divergent budget receipt next completed
    exact (diverges_iff_no_evaluation program input).mp divergent _ receipt.sound
  · intro absent
    apply (diverges_iff_no_evaluation program input).mpr
    intro result evaluation
    obtain ⟨budget, receipt, next, completed, same⟩ := run_complete program input cache result evaluation
    exact absent budget receipt next completed

/-- Actual cycle failures carry the divergence proof for the exact request.
Exhaustion carries no semantic impossibility claim. -/
inductive Failure (program : Generator Input Output) (input : Input) where
  | budgetExhausted
  | cycle (path : List Input) (divergent : Diverges program input)
  deriving Repr

def Failure.diagnostic {Input Output : Type} {program : Generator Input Output} {input : Input} :
    Failure program input → Diagnostic Input
  | .budgetExhausted => .budgetExhausted
  | .cycle path _ => .cycle path

def runCertified [DecidableEq Input] (program : Generator Input Output) (input : Input)
    (budget : Nat) (cache : Cache program := {}) :
    Except (Failure program input) (Receipt program (program input) × Cache program) :=
  match found : run program input budget cache with
  | .ok result => .ok result
  | .error .budgetExhausted => .error .budgetExhausted
  | .error (.cycle path) => .error (.cycle path (run_cycle_diverges program input budget cache path found))

theorem runCertified_diagnostic [DecidableEq Input] (program : Generator Input Output)
    (input : Input) (budget : Nat) (cache : Cache program) :
    (runCertified program input budget cache).mapError Failure.diagnostic = run program input budget cache := by
  unfold runCertified
  split <;> simp_all [Except.mapError, Failure.diagnostic]

end LeanPoo.Prototype.Recursive.Cached
