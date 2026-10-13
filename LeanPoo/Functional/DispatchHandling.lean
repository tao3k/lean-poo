import LeanPoo.Functional.RequestHandling
import LeanPoo.Object.MultimethodSemantics

/-! Checked calls to existing first-class multimethods. Candidate caching and
explicit method state have separate lifetimes; admission runs on every call.
EStateM retains the actual method state on failure. -/
namespace LeanPoo.Functional

inductive DispatchFailure (Error : Type) where
  | input (error : Error)
  | shape (error : Object.MultimethodError)
  | method (error : Error)
  | output (error : Error)
  deriving Repr, BEq

structure DispatchSession (Args Method Output State Error : Type) where
  generic : Object.Multimethod Args Method (EStateM Error State Output)
  state : State

namespace DispatchSession
variable {Args Method Output State Error Approved Wire : Type}

/-- A method-level handler starts from the failed action's returned state.
The handler can itself fail; its own result/state is returned unchanged. -/
def recoverMethod (action : EStateM Error State Output)
    (handler : Error → EStateM Error State Output) : EStateM Error State Output := fun state =>
  match action.run state with
  | .ok value next => .ok value next
  | .error error next => (handler error).run next

theorem recoverMethod_ok (action : EStateM Error State Output)
    (handler : Error → EStateM Error State Output) (state next : State) (value : Output)
    (success : action.run state = .ok value next) :
    (recoverMethod action handler).run state = .ok value next := by
  change (match action.run state with
    | .ok value next => EStateM.Result.ok value next
    | .error error next => (handler error).run next) = _
  rw [success]

theorem recoverMethod_error (action : EStateM Error State Output)
    (handler : Error → EStateM Error State Output) (state next : State) (error : Error)
    (failed : action.run state = .error error next) :
    (recoverMethod action handler).run state = (handler error).run next := by
  change (match action.run state with
    | .ok value next => EStateM.Result.ok value next
    | .error error next => (handler error).run next) = _
  rw [failed]

theorem recoverMethod_handler_error (action : EStateM Error State Output)
    (handler : Error → EStateM Error State Output) (state failedState final : State) (first second : Error)
    (failed : action.run state = .error first failedState)
    (refused : (handler first).run failedState = .error second final) :
    (recoverMethod action handler).run state = .error second final := by
  rw [recoverMethod_error action handler state failedState first failed, refused]

/-- Output admission also runs after an around method bypasses its inner chain. -/
def evaluate (admit : Output → Except Error Approved) (action : EStateM Error State Output)
    (state : State) : Except (DispatchFailure Error) Approved × State :=
  match action.run state with
  | .error error next => (.error (.method error), next)
  | .ok output next => ((admit output).mapError DispatchFailure.output, next)

theorem evaluate_method_error (admit : Output → Except Error Approved)
    (action : EStateM Error State Output) (state next : State) (error : Error)
    (failed : action.run state = .error error next) :
    evaluate admit action state = (.error (.method error), next) := by simp [evaluate, failed]

theorem evaluate_output_error (admit : Output → Except Error Approved)
    (action : EStateM Error State Output) (state next : State) (output : Output) (error : Error)
    (executed : action.run state = .ok output next) (refused : admit output = .error error) :
    evaluate admit action state = (.error (.output error), next) := by simp [evaluate, executed, refused, Except.mapError]

def call (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved) (wire : Wire) :
    RequestResult (DispatchSession Args Method Output State Error) Approved (DispatchFailure Error) :=
  match input.decode wire with
  | .error error => ⟨.error (.input error), session, none⟩
  | .ok args =>
    match session.generic.call args with
    | .error error => ⟨.error (.shape error), session, none⟩
    | .ok (action, updated) =>
      let (outcome, next) := evaluate (admit args) action session.state
      ⟨outcome, ⟨updated, next⟩,
        some (session.generic.cache.get? (session.generic.precedence args)).isSome⟩

theorem call_input_error (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (wire : Wire) (error : Error) (refused : input.decode wire = .error error) :
    session.call input admit wire = ⟨.error (.input error), session, none⟩ := by simp [call, refused]

theorem call_shape_error (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (wire : Wire) (args : Args) (error : Object.MultimethodError)
    (decoded : input.decode wire = .ok args) (failed : session.generic.call args = .error error) :
    session.call input admit wire = ⟨.error (.shape error), session, none⟩ := by simp [call, decoded, failed]

/-- Both successful and refused executions retain the exact updated dispatch
cache and the actual final method state, with the original candidate-hit marker. -/
theorem call_dispatched (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (wire : Wire) (args : Args) (action : EStateM Error State Output)
    (updated : Object.Multimethod Args Method (EStateM Error State Output))
    (decoded : input.decode wire = .ok args) (selected : session.generic.call args = .ok (action, updated)) :
    session.call input admit wire =
      ⟨(evaluate (admit args) action session.state).1,
        ⟨updated, (evaluate (admit args) action session.state).2⟩,
        some (session.generic.cache.get? (session.generic.precedence args)).isSome⟩ := by
  simp only [call, decoded, selected]

def reference (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved) (wire : Wire) :
    Except (DispatchFailure Error) Approved × State :=
  match input.decode wire with
  | .error error => (.error (.input error), session.state)
  | .ok args =>
    match session.generic.referenceCall args with
    | .error error => (.error (.shape error), session.state)
    | .ok action => evaluate (admit args) action session.state

/-- A successful public result has passed the actual input and output gates,
even when an around method omitted the inner computation. -/
theorem call_admitted (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (wire : Wire) (approved : Approved) (success : (session.call input admit wire).outcome = .ok approved) :
    ∃ args output, input.decode wire = .ok args ∧ admit args output = .ok approved := by
  cases decoded : input.decode wire with
  | error error => simp [call, decoded] at success
  | ok args =>
    cases selected : session.generic.call args with
    | error error => simp [call, decoded, selected] at success
    | ok pair =>
      cases executed : pair.1.run session.state with
      | error error next => simp [call, decoded, selected, evaluate, executed] at success
      | ok output next =>
        have admitted : admit args output = .ok approved := by
          cases checked : admit args output <;>
            simp_all [call, evaluate, Except.mapError]
        exact ⟨args, output, rfl, admitted⟩

/-- Complete outcomes and actual method state equal the uncached ordered-tuple
specification. Guard applicability is checked with this call's current args. -/
theorem call_observation (session : DispatchSession Args Method Output State Error)
    (sound : session.generic.CacheSound) (input : Codec Args Wire Error)
    (admit : Args → Output → Except Error Approved) (wire : Wire) :
    ((session.call input admit wire).outcome, (session.call input admit wire).next.state) =
      session.reference input admit wire := by
  cases decoded : input.decode wire with
  | error error => simp [call, reference, decoded]
  | ok args =>
    have correct := session.generic.call_correct sound args
    cases selected : session.generic.call args with
    | error error =>
      have equal : session.generic.referenceCall args = .error error := by simpa [selected, Except.map] using correct.symm
      simp [call, reference, decoded, selected, equal]
    | ok pair =>
      have equal : session.generic.referenceCall args = .ok pair.1 := by simpa [selected, Except.map] using correct.symm
      simp only [call, reference, decoded, selected, equal]

theorem call_cacheSound (session : DispatchSession Args Method Output State Error)
    (sound : session.generic.CacheSound) (input : Codec Args Wire Error)
    (admit : Args → Output → Except Error Approved) (wire : Wire) :
    (session.call input admit wire).next.generic.CacheSound := by
  cases decoded : input.decode wire with
  | error error => simpa [call, decoded] using sound
  | ok args =>
    cases selected : session.generic.call args with
    | error error => simpa [call, decoded, selected] using sound
    | ok pair =>
      simpa only [call, decoded, selected] using session.generic.call_preserves sound args pair.1 pair.2 selected

/-- Input-layout changes preserve the entire result, both states and hit marker. -/
theorem call_represent {Other : Type} (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (pack : Wire → Other) (unpack : Other → Wire) (inverse : ∀ wire, unpack (pack wire) = wire) (wire : Wire) :
    session.call (input.represent pack unpack inverse) admit (pack wire) = session.call input admit wire := by
  simp only [call, Codec.represent_decode]

def callBatch (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved) (wires : List Wire) :
    Except (DispatchFailure Error) (List Approved) × DispatchSession Args Method Output State Error :=
  Validation.traverseState (fun session wire => (session.call input admit wire).transition) session wires

theorem callBatch_error_iff (session final : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (wires : List Wire) (error : DispatchFailure Error) :
    session.callBatch input admit wires = (.error error, final) ↔
      ∃ before wire after outputs next, wires = before ++ wire :: after ∧
        session.callBatch input admit before = (.ok outputs, next) ∧
        (next.call input admit wire).transition = (.error error, final) :=
  Validation.traverseState_error_iff _ _ _ _ _

theorem callBatch_cacheSound (session : DispatchSession Args Method Output State Error)
    (sound : session.generic.CacheSound) (input : Codec Args Wire Error)
    (admit : Args → Output → Except Error Approved) (wires : List Wire) :
    (session.callBatch input admit wires).2.generic.CacheSound :=
  Validation.traverseState_invariant _ (fun session => session.generic.CacheSound)
    (fun current wire valid => current.call_cacheSound valid input admit wire) session sound wires

theorem callBatch_represent {Other : Type} (session : DispatchSession Args Method Output State Error)
    (input : Codec Args Wire Error) (admit : Args → Output → Except Error Approved)
    (pack : Wire → Other) (unpack : Other → Wire) (inverse : ∀ wire, unpack (pack wire) = wire)
    (wires : List Wire) :
    session.callBatch (input.represent pack unpack inverse) admit (wires.map pack) =
      session.callBatch input admit wires := by
  unfold callBatch
  rw [Validation.traverseState_map]
  congr 1
  funext current wire
  rw [call_represent]

end DispatchSession
end LeanPoo.Functional
