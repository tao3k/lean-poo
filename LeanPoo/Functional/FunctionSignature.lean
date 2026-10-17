import LeanPoo.Functional.Validation

/-! Finite declarative call signatures. These laws describe supplied arguments and
ordered dispatch; host default evaluation and native procedure arity remain premises. -/
namespace LeanPoo.Functional.FunctionSignature

/-- Required and optional positions, rest permission, and declared/required keys. -/
structure Signature (Key : Type) where
  required : Nat
  optional : Nat := 0
  rest : Bool := false
  keywords : List Key := []
  requiredKeywords : List Key := []
  deriving Repr, DecidableEq

/-- A decoded call retains supplied values only; absent defaults have no entry. -/
structure Call (Key Value : Type) where
  positional : List Value
  keywords : List (Key × Value) := []
  deriving Repr, DecidableEq

/-- Reject duplicate keys as well as arity, unknown-key and missing-key errors. -/
def accepts [DecidableEq Key] (signature : Signature Key) (call : Call Key Value) : Bool :=
  decide (signature.required ≤ call.positional.length) &&
  (signature.rest || decide (call.positional.length ≤ signature.required + signature.optional)) &&
  decide ((call.keywords.map Prod.fst).Nodup) &&
  call.keywords.all (fun entry => decide (entry.1 ∈ signature.keywords)) &&
  signature.requiredKeywords.all (fun key => decide (key ∈ call.keywords.map Prod.fst))

/-- Dispatch by the first structural match, before invoking any type check. -/
def select [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value) :=
  signatures.find? (accepts · call)

/-- A matching earlier clause shadows all later clauses, regardless of value types. -/
theorem select_first [DecidableEq Key] (head : Signature Key) (tail) (call : Call Key Value)
    (matched : accepts head call = true) : select (head :: tail) call = some head := by
  simp [select, List.find?, matched]

/-- Selection returns a member of the declared sequence with an accepted shape. -/
theorem select_sound [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value)
    (signature) (selected : select signatures call = some signature) :
    signature ∈ signatures ∧ accepts signature call = true := by
  induction signatures with
  | nil => simp [select, List.find?] at selected
  | cons head tail ih =>
    by_cases matched : accepts head call = true
    · have same : head = signature := by simpa [select, List.find?, matched] using selected
      subst signature
      exact ⟨by simp, matched⟩
    · have later : select tail call = some signature := by
        simpa [select, List.find?, matched] using selected
      obtain ⟨member, shape⟩ := ih later
      exact ⟨by simp [member], shape⟩

/-- An ill-shaped call cannot reach normalization or the body. -/
def invoke [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value)
    (shapeError : Error) (normalize : Signature Key → Call Key Value → Except Error (Call Key Value))
    (body : Call Key Value → Except Error Result) : Except Error Result :=
  match select signatures call with
  | none => .error shapeError
  | some signature => (normalize signature call).bind body

/-- Structural refusal has no body branch. -/
theorem invoke_shape_error [DecidableEq Key] (signatures) (call : Call Key Value)
    (shapeError : Error) (normalize) (body : Call Key Value → Except Error Result)
    (refused : select signatures call = none) :
    invoke signatures call shapeError normalize body = .error shapeError := by
  simp [invoke, refused]

/-- Type refusal preserves its error and never falls through to another signature. -/
theorem invoke_type_error [DecidableEq Key] (signatures) (call : Call Key Value)
    (shapeError error : Error) (normalize) (body : Call Key Value → Except Error Result)
    (signature) (selected : select signatures call = some signature)
    (refused : normalize signature call = .error error) :
    invoke signatures call shapeError normalize body = .error error := by
  simp [invoke, selected, refused, Except.bind]

/-- Ordered field checking preserves supplied cardinality, so it cannot insert or
execute missing optional defaults. The host remains responsible for those defaults. -/
theorem supplied_length (check : Value → Except Error Value) (values checked : List Value)
    (success : Validation.traverse check values = .ok checked) : checked.length = values.length := by
  induction values generalizing checked with
  | nil => simp [Validation.traverse] at success; subst checked; rfl
  | cons head tail ih =>
    simp only [Validation.traverse] at success
    cases h : check head with
    | error error => simp [h, Except.bind] at success
    | ok value =>
      cases t : Validation.traverse check tail with
      | error error => simp [h, t, Except.bind, Except.map] at success
      | ok rest =>
        simp [h, t, Except.bind, Except.map] at success
        subst checked
        simp [ih rest t]

end LeanPoo.Functional.FunctionSignature
