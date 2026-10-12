import LeanPoo.Object.Callable
import LeanPoo.Prototype.DynamicSchema

/-! Runtime descriptor boundaries for actual recursive method calls. The
same registered FunctionOf descriptors used by ordinary function references
describe parameterized object methods; successful calls retain the evaluation
proof and input/output membership proofs for the values that crossed the gate. -/
namespace LeanPoo.Object.Callable

open Prototype
open Prototype.Recursive
open Prototype.CallableRecord

structure Signature where
  name : String
  input : Dynamic.Contract
  output : Dynamic.Contract
  deriving Repr

def Signature.fromDescriptor (name : String) (descriptor : Dynamic.Descriptor) :
    Except Dynamic.Error Signature :=
  match descriptor.contract with
  | .functionOf input output => .ok ⟨name, input, output⟩
  | _ => .error .expectedFunctionContract

def Signature.argumentType (signature : Signature) : Dynamic.Descriptor :=
  ⟨s!"{signature.name} argument", signature.input, []⟩

def Signature.resultType (signature : Signature) : Dynamic.Descriptor :=
  ⟨s!"{signature.name} result", signature.output, []⟩

inductive InvokeError where
  | signature (error : Dynamic.Error)
  | schema (error : Dynamic.SchemaError)
  | argument (error : Dynamic.WireError)
  | result (error : Dynamic.WireError)
  | source (message : String)
  | diagnostic (error : Cached.Diagnostic (Request Dynamic.Value))
  deriving Repr

structure CheckedCall (program : Prototype.CallableRecord.Self Dynamic.Value) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) where
  value : Dynamic.Value
  evaluation : Evaluates program (program ⟨signature.name, argument⟩) (.value value)
  inputAccepted : Dynamic.Accepted registry signature.input argument
  outputAccepted : Dynamic.Accepted registry signature.output value

abbrev Invocation (plan : Plan Dynamic.Value) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) :=
  CheckedCall plan.program registry signature argument

def CheckedCall.fromReceipt {program : Prototype.CallableRecord.Self Dynamic.Value}
    (registry : Dynamic.Registry) (signature : Signature) (argument : Dynamic.Value) (fuel : Nat)
    (inputAccepted : Dynamic.Accepted registry signature.input argument)
    (receipt : Cached.Receipt program (program ⟨signature.name, argument⟩)) :
    Except InvokeError (CheckedCall program registry signature argument) :=
  match receipt with
  | ⟨.error message, _⟩ => .error (.source message)
  | ⟨.value value, evaluated⟩ =>
    match checkedOutput : signature.resultType.validate registry fuel value with
    | .error error => .error (.result error)
    | .ok admittedOutput =>
      have sameOutput := signature.resultType.validate_value registry fuel value
        admittedOutput checkedOutput
      .ok ⟨value, evaluated, inputAccepted, sameOutput ▸ admittedOutput.valid⟩

variable {plan : Plan Dynamic.Value}

/-- Input validation runs before the object method can be forced. Output
validation runs on every call, including a hot memo hit, in the current registry. -/
def Instance.invoke (instanceValue : Instance plan) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat) :
    IO (Except InvokeError (Invocation plan registry signature argument)) := do
  match checkedInput : signature.argumentType.validate registry fuel argument with
  | .error error => return .error (.argument error)
  | .ok admittedInput =>
    match ← instanceValue.call budget ⟨signature.name, argument⟩ with
    | .error diagnostic => return .error (.diagnostic diagnostic)
    | .ok receipt =>
      have sameInput := signature.argumentType.validate_value registry fuel argument
        admittedInput checkedInput
      return CheckedCall.fromReceipt registry signature argument fuel
        (sameInput ▸ admittedInput.valid) receipt

/-- A descriptor produced by a runtime FunctionOf factory is directly usable
as an object method's checked calling convention. -/
def Instance.invokeDescriptor (instanceValue : Instance plan) (registry : Dynamic.Registry)
    (name : String) (descriptor : Dynamic.Descriptor) (argument : Dynamic.Value)
    (budget fuel : Nat) :
    IO (Except InvokeError Dynamic.Value) := do
  match Signature.fromDescriptor name descriptor with
  | .error error => return .error (.signature error)
  | .ok signature =>
    let result ← instanceValue.invoke registry signature argument budget fuel
    return result.map (fun invocation => invocation.value)

/-- Reflective slot catalogs already carry the registered type identity.
Resolve that identity on each invocation instead of copying a second signature. -/
def Instance.invokeSlot (instanceValue : Instance plan) (registry : Dynamic.Registry)
    (slot : Dynamic.SlotDescription) (argument : Dynamic.Value) (budget fuel : Nat) :
    IO (Except InvokeError Dynamic.Value) := do
  match registry.resolveDescriptor (.descriptor slot.typeIdentity) with
  | .error error => return .error (.schema error)
  | .ok descriptor =>
    instanceValue.invokeDescriptor registry slot.name descriptor argument budget fuel

theorem Invocation.observed (invocation : Invocation plan registry signature argument) :
    ∃ depth, plan.call depth ⟨signature.name, argument⟩ = .value invocation.value :=
  solve_complete invocation.evaluation

end LeanPoo.Object.Callable

namespace LeanPoo.Prototype.CallableRecord

open Recursive
open Object.Callable

/-- A checked mutable invocation exposes the exact retained snapshot along
with its evaluation and boundary proofs. Later writes cannot relabel it. -/
def Mutable.invoke (object : Mutable Dynamic.Value) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat) :
    IO (Except InvokeError (Σ snapshot : Snapshot Dynamic.Value,
      CheckedCall (generator snapshot.storage) registry signature argument)) := do
  match checkedInput : signature.argumentType.validate registry fuel argument with
  | .error error => return .error (.argument error)
  | .ok admittedInput =>
    let ⟨snapshot, result⟩ ← object.callCertified budget ⟨signature.name, argument⟩
    match result with
    | .error failure => return .error (.diagnostic failure.diagnostic)
    | .ok receipt =>
      have sameInput := signature.argumentType.validate_value registry fuel argument
        admittedInput checkedInput
      return (CheckedCall.fromReceipt registry signature argument fuel
        (sameInput ▸ admittedInput.valid) receipt).map (fun invocation => ⟨snapshot, invocation⟩)

end LeanPoo.Prototype.CallableRecord
