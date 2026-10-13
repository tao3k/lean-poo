import LeanPoo.Functional.RequestHandling
import LeanPoo.Object.CallableValidation
import LeanPoo.Prototype.DynamicCodecSemantics

/-! Pure checked calls to existing recursive method programs. Memo entries
retain evaluation proofs for the program; admission belongs to the current
registry and is repeated even when that method request is already memoized. -/
namespace LeanPoo.Functional
open Prototype Prototype.Recursive Prototype.CallableRecord Object.Callable

inductive RecursiveFailure (program : Prototype.CallableRecord.Self Dynamic.Value) where
  | boundary (error : InvokeError)
  | evaluation (request : Request Dynamic.Value) (failure : Cached.Failure program request)
  deriving Repr

structure RecursiveSession (program : Prototype.CallableRecord.Self Dynamic.Value) where
  memo : Cached.Cache program := {}

/-- The calling convention is resolved from this registry, with its exact
catalog identity retained alongside evaluation and input/output admission. -/
structure CatalogInvocation (program : Prototype.CallableRecord.Self Dynamic.Value)
    (registry : Dynamic.Registry) (slot : Dynamic.SlotDescription) (argument : Dynamic.Value) where
  descriptor : Dynamic.Descriptor
  resolved : registry.resolveDescriptor (.descriptor slot.typeIdentity) = .ok descriptor
  signature : Signature
  selected : Signature.fromDescriptor slot.name descriptor = .ok signature
  checked : CheckedCall program registry signature argument

structure CatalogRequest where
  slot : Dynamic.SlotDescription
  argument : Dynamic.Value
  deriving Repr, BEq

structure CatalogAnswer (program : Prototype.CallableRecord.Self Dynamic.Value)
    (registry : Dynamic.Registry) where
  request : CatalogRequest
  invocation : CatalogInvocation program registry request.slot request.argument

namespace RecursiveSession
variable {program : Prototype.CallableRecord.Self Dynamic.Value}

def call (session : RecursiveSession program) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat) :
    RequestResult (RecursiveSession program) (CheckedCall program registry signature argument)
      (RecursiveFailure program) :=
  match checkedInput : signature.argumentType.validate registry fuel argument with
  | .error error => ⟨.error (.boundary (.argument error)), session, none⟩
  | .ok admittedInput =>
    let reused := some (session.memo.lookup ⟨signature.name, argument⟩).isSome
    match Cached.runCertified program ⟨signature.name, argument⟩ budget session.memo with
    | .error failure => ⟨.error (.evaluation ⟨signature.name, argument⟩ failure), session, reused⟩
    | .ok (receipt, next) =>
      let same := signature.argumentType.validate_value registry fuel argument admittedInput checkedInput
      ⟨(CheckedCall.fromReceipt registry signature argument fuel
          (same ▸ admittedInput.valid) receipt).mapError RecursiveFailure.boundary, ⟨next⟩, reused⟩

theorem call_input_error (session : RecursiveSession program) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat) (error : Dynamic.WireError)
    (refused : signature.argumentType.validate registry fuel argument = .error error) :
    session.call registry signature argument budget fuel =
      ⟨.error (.boundary (.argument error)), session, none⟩ := by
  unfold call
  split <;> simp_all

/-- Incomplete runs publish no new memo state, matching the existing executor.
A cycle failure retains its divergence proof; exhaustion carries no such proof. -/
theorem call_diagnostic (session : RecursiveSession program) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat)
    (admitted : Dynamic.Admitted registry signature.input)
    (valid : signature.argumentType.validate registry fuel argument = .ok admitted)
    (failure : Cached.Failure program ⟨signature.name, argument⟩)
    (failed : Cached.runCertified program ⟨signature.name, argument⟩ budget session.memo = .error failure) :
    session.call registry signature argument budget fuel =
      ⟨.error (.evaluation ⟨signature.name, argument⟩ failure), session,
        some (session.memo.lookup ⟨signature.name, argument⟩).isSome⟩ := by
  unfold call
  split <;> simp_all

/-- Completed source errors and output refusals keep the exact completed memo,
while successful results retain the same program-indexed evaluation receipt. -/
theorem call_completed (session : RecursiveSession program) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat)
    (admitted : Dynamic.Admitted registry signature.input)
    (valid : signature.argumentType.validate registry fuel argument = .ok admitted)
    (receipt : Cached.Receipt program (program ⟨signature.name, argument⟩)) (next : Cached.Cache program)
    (completed : Cached.runCertified program ⟨signature.name, argument⟩ budget session.memo = .ok (receipt, next)) :
    session.call registry signature argument budget fuel =
      ⟨(CheckedCall.fromReceipt registry signature argument fuel
        ((signature.argumentType.validate_value registry fuel argument admitted valid) ▸ admitted.valid)
        receipt).mapError RecursiveFailure.boundary, ⟨next⟩,
        some (session.memo.lookup ⟨signature.name, argument⟩).isSome⟩ := by
  unfold call
  split <;> simp_all

theorem value_agrees (checked : CheckedCall program registry signature argument)
    (depth : Nat) (known : solve program depth ⟨signature.name, argument⟩ ≠ .pending) :
    solve program depth ⟨signature.name, argument⟩ = .value checked.value :=
  (⟨.value checked.value, checked.evaluation⟩ :
    Cached.Receipt program (program ⟨signature.name, argument⟩)).agrees depth known

/-- Different current registries can admit the same program request under
different contracts, but cannot change its actual evaluated value. -/
theorem admitted_values_agree
    (left : CheckedCall program leftRegistry leftSignature argument)
    (right : CheckedCall program rightRegistry rightSignature argument)
    (sameName : leftSignature.name = rightSignature.name) : left.value = right.value := by
  obtain ⟨depth, observed⟩ := solve_complete left.evaluation
  have sameRequest : (⟨leftSignature.name, argument⟩ : Request Dynamic.Value) =
      ⟨rightSignature.name, argument⟩ := by rw [sameName]
  have agrees := value_agrees right depth (by rw [← sameRequest, observed]; simp)
  rw [← sameRequest, observed] at agrees
  exact Observation.value.inj agrees

def callSlot (session : RecursiveSession program) (registry : Dynamic.Registry)
    (slot : Dynamic.SlotDescription) (argument : Dynamic.Value) (budget fuel : Nat) :
    RequestResult (RecursiveSession program) (CatalogInvocation program registry slot argument)
      (RecursiveFailure program) :=
  match resolved : registry.resolveDescriptor (.descriptor slot.typeIdentity) with
  | .error error => ⟨.error (.boundary (.schema error)), session, none⟩
  | .ok descriptor =>
    match selected : Signature.fromDescriptor slot.name descriptor with
    | .error error => ⟨.error (.boundary (.signature error)), session, none⟩
    | .ok signature =>
      let result := session.call registry signature argument budget fuel
      ⟨result.outcome.map (fun checked => ⟨descriptor, resolved, signature, selected, checked⟩),
        result.next, result.reused⟩

theorem callSlot_schema_error (session : RecursiveSession program) (registry : Dynamic.Registry)
    (slot : Dynamic.SlotDescription) (argument : Dynamic.Value) (budget fuel : Nat) (error : Dynamic.SchemaError)
    (refused : registry.resolveDescriptor (.descriptor slot.typeIdentity) = .error error) :
    session.callSlot registry slot argument budget fuel =
      ⟨.error (.boundary (.schema error)), session, none⟩ := by
  unfold callSlot
  split <;> simp_all

theorem callSlot_signature_error (session : RecursiveSession program) (registry : Dynamic.Registry)
    (slot : Dynamic.SlotDescription) (argument : Dynamic.Value) (budget fuel : Nat)
    (descriptor : Dynamic.Descriptor) (error : Dynamic.Error)
    (resolved : registry.resolveDescriptor (.descriptor slot.typeIdentity) = .ok descriptor)
    (refused : Signature.fromDescriptor slot.name descriptor = .error error) :
    session.callSlot registry slot argument budget fuel =
      ⟨.error (.boundary (.signature error)), session, none⟩ := by
  unfold callSlot
  split
  · simp_all
  · rename_i actual found
    have same : actual = descriptor := Except.ok.inj (found.symm.trans resolved)
    subst actual
    split <;> simp_all

def callRequest (session : RecursiveSession program) (registry : Dynamic.Registry)
    (request : CatalogRequest) (budget fuel : Nat) :
    RequestResult (RecursiveSession program) (CatalogAnswer program registry) (RecursiveFailure program) :=
  let result := session.callSlot registry request.slot request.argument budget fuel
  ⟨result.outcome.map (fun invocation => ⟨request, invocation⟩), result.next, result.reused⟩

theorem callRequest_request (session : RecursiveSession program) (registry : Dynamic.Registry)
    (request : CatalogRequest) (budget fuel : Nat) (answer : CatalogAnswer program registry)
    (success : (session.callRequest registry request budget fuel).outcome = .ok answer) :
    answer.request = request := by
  unfold callRequest at success
  cases result : (session.callSlot registry request.slot request.argument budget fuel).outcome <;>
    simp_all [Except.map]
  cases success
  rfl

def callBatch (session : RecursiveSession program) (registry : Dynamic.Registry)
    (requests : List CatalogRequest) (budget fuel : Nat) :
    Except (RecursiveFailure program) (List (CatalogAnswer program registry)) × RecursiveSession program :=
  Validation.traverseState (fun current request => (current.callRequest registry request budget fuel).transition)
    session requests

theorem callBatch_error_iff (session final : RecursiveSession program) (registry : Dynamic.Registry)
    (requests : List CatalogRequest) (budget fuel : Nat) (error : RecursiveFailure program) :
    session.callBatch registry requests budget fuel = (.error error, final) ↔
      ∃ before request after answers next, requests = before ++ request :: after ∧
        session.callBatch registry before budget fuel = (.ok answers, next) ∧
        (next.callRequest registry request budget fuel).transition = (.error error, final) :=
  Validation.traverseState_error_iff _ _ _ _ _

theorem callBatch_requests (session final : RecursiveSession program) (registry : Dynamic.Registry)
    (requests : List CatalogRequest) (budget fuel : Nat) (answers : List (CatalogAnswer program registry))
    (success : session.callBatch registry requests budget fuel = (.ok answers, final)) :
    answers.map CatalogAnswer.request = requests :=
  Validation.traverseState_project _ _
    (fun current request answer _next completed =>
      current.callRequest_request registry request budget fuel answer (congrArg Prod.fst completed))
    session final requests answers success

theorem callBatch_append (session : RecursiveSession program) (registry : Dynamic.Registry)
    (left right : List CatalogRequest) (budget fuel : Nat) :
    session.callBatch registry (left ++ right) budget fuel =
      match session.callBatch registry left budget fuel with
      | (.error error, final) => (.error error, final)
      | (.ok before, next) =>
        let (after, final) := next.callBatch registry right budget fuel
        (after.map (before ++ ·), final) :=
  by
    simp only [callBatch]
    rw [Validation.traverseState_append]
    cases Validation.traverseState
        (fun current request => (current.callRequest registry request budget fuel).transition) session left with
    | mk outcome next =>
      cases outcome with
      | error error => rfl
      | ok before =>
        cases Validation.traverseState
          (fun current request => (current.callRequest registry request budget fuel).transition) next right
        rfl

end RecursiveSession

namespace CatalogInvocation
theorem method_name (invocation : CatalogInvocation program registry slot argument) :
    invocation.signature.name = slot.name := by
  have selected := invocation.selected
  unfold Signature.fromDescriptor at selected
  split at selected <;> simp_all
  exact (congrArg Signature.name selected).symm

theorem observed (invocation : CatalogInvocation program registry slot argument) :
    ∃ depth, solve program depth ⟨slot.name, argument⟩ = .value invocation.checked.value := by
  have observation := solve_complete invocation.checked.evaluation
  rw [invocation.method_name] at observation
  exact observation

def encodeJson (invocation : CatalogInvocation program registry slot argument) : Lean.Json :=
  invocation.checked.value.encodeJson

theorem decode_encode (invocation : CatalogInvocation program registry slot argument)
    (fuel : Nat) (bound : invocation.checked.value.wireDepth ≤ fuel) :
    Dynamic.Value.decodeJson fuel invocation.encodeJson = .ok invocation.checked.value :=
  invocation.checked.value.decodeJson_encodeJson fuel bound
end CatalogInvocation
end LeanPoo.Functional
