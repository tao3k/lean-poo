import LeanPoo.Functional.FunctionValidation

/-! FUN wrapper admission with explicit outer membership and payload normalization.
The host supplies faithful wrap/unwrap operations and its identity-reuse policy.
Callbacks are pure/terminating here; function carriers need no decidable equality. -/
namespace LeanPoo.Functional.WrapperValidation

/-- One outer admission boundary, reused before and after payload validation. -/
def admit (member : Carrier → Bool) (failure : Error) (value : Carrier) : Except Error Carrier :=
  if member value then .ok value else .error failure

/-- Preserve the original carrier when the supplied rebuild policy permits it.
The underlying validator can replace a raw function by a checked function. -/
def validate (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure : Error) (value : Carrier) : Except Error Carrier :=
  ObjectContract.checkedAction (admit member failure)
    (fun original => (check (unwrap original)).bind fun checked =>
      admit member failure (rebuild original checked)) value

/-- Invalid outer carriers refuse before unwrap or payload normalization. -/
theorem outer_error (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure : Error) (value : Carrier) (invalid : member value = false) :
    validate member unwrap check rebuild failure value = .error failure := by
  simp [validate, ObjectContract.checkedAction, admit, invalid, Except.bind]

/-- A payload error, including an opaque false-like cause, is retained exactly. -/
theorem payload_error (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure cause : Error) (value : Carrier) (valid : member value = true)
    (refused : check (unwrap value) = .error cause) :
    validate member unwrap check rebuild failure value = .error cause := by
  simp [validate, ObjectContract.checkedAction, admit, valid, refused, Except.bind]

/-- Success exposes the actual normalized payload and the final membership gate.
No replacement carrier can bypass a refinement on the outer representation. -/
theorem success_iff (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure : Error) (value result : Carrier) :
    validate member unwrap check rebuild failure value = .ok result ↔
      member value = true ∧ ∃ payload, check (unwrap value) = .ok payload ∧
        member (rebuild value payload) = true ∧ rebuild value payload = result := by
  cases h : member value <;> simp [validate, ObjectContract.checkedAction, admit, h, Except.bind]
  case true =>
    cases hc : check (unwrap value) <;> simp
    case ok payload => cases member (rebuild value payload) <;> simp

/-- Unchanged payloads retain the exact original carrier, under the host's reuse law. -/
theorem unchanged (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure : Error) (value : Carrier) (valid : member value = true)
    (same : check (unwrap value) = .ok (unwrap value))
    (reuse : rebuild value (unwrap value) = value) :
    validate member unwrap check rebuild failure value = .ok value := by
  simp [validate, ObjectContract.checkedAction, admit, valid, same, reuse, Except.bind]

/-- Lawful wrapping retains the *checked* function's behavior, not the raw source.
Combined with FunctionValidation.input_error/returned, both call gates survive. -/
theorem checked_payload (member : Carrier → Bool) (unwrap : Carrier → Payload)
    (check : Payload → Except Error Payload) (rebuild : Carrier → Payload → Carrier)
    (failure : Error) (value result : Carrier)
    (law : ∀ original payload, unwrap (rebuild original payload) = payload)
    (accepted : validate member unwrap check rebuild failure value = .ok result) :
    check (unwrap value) = .ok (unwrap result) := by
  obtain ⟨_, payload, checked, _, rfl⟩ := (success_iff _ _ _ _ _ _ _).mp accepted
  simpa [law] using checked
end LeanPoo.Functional.WrapperValidation
