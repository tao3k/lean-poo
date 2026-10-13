import LeanPoo.Functional.RecursiveDispatch

/-! Re-admit completed, program-indexed answers under a current catalog.
The original request and evaluation are retained; only descriptor boundaries
are checked. This operation has no evaluator, memo session or evaluation budget. -/
namespace LeanPoo.Functional.RecursiveDispatch
open Prototype Prototype.CallableRecord Prototype.Recursive Object.Callable
variable {program : CallableRecord.Self Dynamic.Value} {Ledger : Type}

structure ReAdmission (original : Answer program) (current : Dynamic.Registry) where
  receipt : Receipt program current original.request
  sameValue : receipt.invocation.checked.value = original.value

private theorem signature_name (name : String) (descriptor : Dynamic.Descriptor) (signature : Signature)
    (selected : Signature.fromDescriptor name descriptor = .ok signature) : signature.name = name := by
  unfold Signature.fromDescriptor at selected
  split at selected <;> simp_all
  exact (congrArg Signature.name selected).symm

/-- Current lookup, signature, input and output checks run in that order.
No change of program, request or result is permitted by the return type. -/
def Answer.revalidate (original : Answer program) (current : Dynamic.Registry) (fuel : Nat) :
    Except InvokeError (ReAdmission original current) :=
  match resolved : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) with
  | .error error => .error (.schema error)
  | .ok descriptor =>
    match selected : Signature.fromDescriptor original.request.slot.name descriptor with
    | .error error => .error (.signature error)
    | .ok signature =>
      match checkedInput : signature.argumentType.validate current fuel original.request.argument with
      | .error error => .error (.argument error)
      | .ok admittedInput =>
        match checkedOutput : signature.resultType.validate current fuel original.value with
        | .error error => .error (.result error)
        | .ok admittedOutput =>
          have sameInput := signature.argumentType.validate_value current fuel original.request.argument admittedInput checkedInput
          have sameOutput := signature.resultType.validate_value current fuel original.value admittedOutput checkedOutput
          have evaluated : Evaluates program (program ⟨signature.name, original.request.argument⟩) (.value original.value) := by
            rw [signature_name _ _ _ selected, ← original.receipt.invocation.method_name]
            exact original.receipt.invocation.checked.evaluation
          .ok ⟨⟨⟨descriptor, resolved, signature, selected,
            ⟨original.value, evaluated, sameInput ▸ admittedInput.valid, sameOutput ▸ admittedOutput.valid⟩⟩, none⟩, rfl⟩

def ReAdmission.answer {original : Answer program} {current : Dynamic.Registry}
    (admission : ReAdmission original current) : Answer program :=
  ⟨current, original.request, admission.receipt⟩

theorem ReAdmission.value {original : Answer program} {current : Dynamic.Registry}
    (admission : ReAdmission original current) : admission.answer.value = original.value := admission.sameValue

theorem ReAdmission.request {original : Answer program} {current : Dynamic.Registry}
    (admission : ReAdmission original current) : admission.answer.request = original.request := rfl

theorem ReAdmission.observed {original : Answer program} {current : Dynamic.Registry}
    (admission : ReAdmission original current) :
    ∃ depth, solve program depth ⟨original.request.slot.name, original.request.argument⟩ = .value original.value := by
  simpa [admission.sameValue] using admission.receipt.observed

theorem ReAdmission.outputAccepted {original : Answer program} {current : Dynamic.Registry}
    (admission : ReAdmission original current) :
    Dynamic.Accepted current admission.receipt.invocation.signature.output original.value := by
  rw [← admission.sameValue]
  exact admission.receipt.outputAccepted

theorem Answer.revalidate_noRead (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (admission : ReAdmission original current) (accepted : original.revalidate current fuel = .ok admission) :
    admission.receipt.reused = none := by
  unfold Answer.revalidate at accepted
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  rw [← accepted]

theorem Answer.revalidate_schema_error (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (error : Dynamic.SchemaError)
    (missing : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) = .error error) :
    original.revalidate current fuel = .error (.schema error) := by
  unfold Answer.revalidate
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)


theorem Answer.revalidate_signature_error (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (descriptor : Dynamic.Descriptor) (error : Dynamic.Error)
    (resolved : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) = .ok descriptor)
    (invalid : Signature.fromDescriptor original.request.slot.name descriptor = .error error) :
    original.revalidate current fuel = .error (.signature error) := by
  unfold Answer.revalidate
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)


theorem Answer.revalidate_argument_error (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (descriptor : Dynamic.Descriptor) (signature : Signature) (error : Dynamic.WireError)
    (resolved : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) = .ok descriptor)
    (selected : Signature.fromDescriptor original.request.slot.name descriptor = .ok signature)
    (invalid : signature.argumentType.validate current fuel original.request.argument = .error error) :
    original.revalidate current fuel = .error (.argument error) := by
  unfold Answer.revalidate
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)


theorem Answer.revalidate_result_error (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (descriptor : Dynamic.Descriptor) (signature : Signature) (error : Dynamic.WireError)
    (admitted : Dynamic.Admitted current signature.argumentType.contract)
    (resolved : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) = .ok descriptor)
    (selected : Signature.fromDescriptor original.request.slot.name descriptor = .ok signature)
    (input : signature.argumentType.validate current fuel original.request.argument = .ok admitted)
    (invalid : signature.resultType.validate current fuel original.value = .error error) :
    original.revalidate current fuel = .error (.result error) := by
  unfold Answer.revalidate
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)


theorem Answer.revalidate_complete (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (descriptor : Dynamic.Descriptor) (signature : Signature)
    (admittedInput : Dynamic.Admitted current signature.argumentType.contract)
    (admittedOutput : Dynamic.Admitted current signature.resultType.contract)
    (resolved : current.resolveDescriptor (.descriptor original.request.slot.typeIdentity) = .ok descriptor)
    (selected : Signature.fromDescriptor original.request.slot.name descriptor = .ok signature)
    (input : signature.argumentType.validate current fuel original.request.argument = .ok admittedInput)
    (output : signature.resultType.validate current fuel original.value = .ok admittedOutput) :
    ∃ admission, original.revalidate current fuel = .ok admission := by
  unfold Answer.revalidate
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)
  split <;> (try simp_all) <;> subst_vars <;> (try simp_all)

/-- Retained-state method adapter: boundary refusal is an ordinary method error.
Neither success nor failure touches memo entries, statistics, ledger or read marker. -/
def Answer.revalidateMethod (original : Answer program) (current : Dynamic.Registry) (fuel : Nat) :
    EStateM (Error program) (State program Ledger) (Answer program) := fun state =>
  match original.revalidate current fuel with
  | .error error => .error (.recursive (.boundary error)) state
  | .ok admission => .ok admission.answer state

theorem Answer.revalidateMethod_state (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (state : State program Ledger) :
    returnedState ((original.revalidateMethod current fuel).run state) = state := by
  simp only [Answer.revalidateMethod, EStateM.run]
  split <;> rfl

theorem Answer.revalidateMethod_error (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (state : State program Ledger) (error : InvokeError)
    (refused : original.revalidate current fuel = .error error) :
    (original.revalidateMethod current fuel).run state = .error (.recursive (.boundary error)) state := by
  simp [Answer.revalidateMethod, EStateM.run, refused]

theorem Answer.revalidateMethod_ok (original : Answer program) (current : Dynamic.Registry) (fuel : Nat)
    (state : State program Ledger) (admission : ReAdmission original current)
    (accepted : original.revalidate current fuel = .ok admission) :
    (original.revalidateMethod current fuel).run state = .ok admission.answer state := by
  simp [Answer.revalidateMethod, EStateM.run, accepted]

end LeanPoo.Functional.RecursiveDispatch
