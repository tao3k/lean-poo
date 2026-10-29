import LeanPoo.Functional.PropertyGenerators

/-! Finite sequence preparation. Malformed host spines are represented by none;
accurate shape conversion, source observers and terminating callbacks are premises.
The general lazy Iterator protocol is deliberately not constrained here. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Reject malformed spines before entering model/candidate preparation. Empty
proper lists remain present data and retain their ordinary preparation behavior. -/
def finiteSequenceInput (invalid : Cause) (input : Option (List Value))
    (prepare : List Value → Except (Option Cause) Output) : Except (Option Cause) Output :=
  match input with
  | none => .error (some invalid)
  | some values => prepare values

/-- A parameter callback first satisfies the existing source boundary, then its
returned finite shape. Source revision therefore precedes normal-result admission;
original callback exceptions retain their cause. No partial batch is published. -/
def finiteShrinkStage (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) : Except (Option Cause) (List Output × State) :=
  match guardedGeneration live (shrink value) state with
  | .error cause => .error cause
  | .ok (none, _) => .error (some invalid)
  | .ok (some values, next) => .ok (values, next)

/-- No initializer or candidate repair is reachable after malformed input. -/
theorem finiteSequenceInput_refused (invalid : Cause)
    (prepare : List Value → Except (Option Cause) Output) :
    finiteSequenceInput invalid none prepare = .error (some invalid) := rfl

/-- A proper input is forwarded exactly, including an empty list. -/
theorem finiteSequenceInput_present (invalid : Cause) (values : List Value)
    (prepare : List Value → Except (Option Cause) Output) :
    finiteSequenceInput invalid (some values) prepare = prepare values := rfl

/-- Already obsolete preparation cannot invoke its parameter callback. -/
theorem finiteShrinkStage_stale (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) (stale : live state = false) :
    finiteShrinkStage live invalid shrink value state = .error none := by
  simp [finiteShrinkStage, guardedGeneration, stale]

/-- Normal callback revision skips shape admission and the next coordinate. -/
theorem finiteShrinkStage_revised (live : State → Bool) (invalid : Cause)
    (values : Option (List Output)) (value : Value) (state next : State)
    (before : live state = true) (after : live next = false) :
    finiteShrinkStage live invalid (fun _ _ => .ok (values, next)) value state = .error none := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Callback exceptions remain exact even when normal-result checks would fail. -/
theorem finiteShrinkStage_cause (live : State → Bool) (invalid cause : Cause)
    (value : Value) (state : State) (before : live state = true) :
    finiteShrinkStage (Output := Output) live invalid (fun _ _ => .error cause) value state =
      .error (some cause) := by
  simp [finiteShrinkStage, guardedGeneration, before]

/-- An admitted callback's malformed result is an error, never a usable prefix. -/
theorem finiteShrinkStage_malformed (live : State → Bool) (invalid : Cause)
    (value : Value) (state next : State) (before : live state = true) (after : live next = true) :
    finiteShrinkStage (Output := Output) live invalid (fun _ _ => .ok (none, next)) value state =
      .error (some invalid) := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Proper result order, false payloads and the resulting state are unchanged. -/
theorem finiteShrinkStage_present (live : State → Bool) (invalid : Cause)
    (values : List Output) (value : Value) (state next : State)
    (before : live state = true) (after : live next = true) :
    finiteShrinkStage live invalid (fun _ _ => .ok (some values, next)) value state = .ok (values, next) := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Either source or shape refusal prevents every later preparation stage. -/
theorem finiteShrinkStage_refused (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) (cause : Option Cause)
    (next : List Output × State → Except (Option Cause) Other)
    (refused : finiteShrinkStage live invalid shrink value state = .error cause) :
    (finiteShrinkStage live invalid shrink value state >>= next) = .error cause := by
  rw [refused]; rfl

/-- Admission does not change legitimate dependency retirement: only normalized
commands may be omitted by the existing model policy, in original relative order. -/
theorem finiteSequenceInput_repair (model : TraceModel State Command Reply)
    (invalid : Cause) (commands : List Command) (state : State) :
    finiteSequenceInput invalid (some commands)
      (fun values => .ok (retire model state values)) = .ok (retire model state commands) ∧
      traceValid model state (retire model state commands) = true ∧
      (retire model state commands).Sublist commands :=
  ⟨rfl, retire_valid model commands state, retire_sublist model commands state⟩

end LeanPoo.Functional.PropertyTesting
