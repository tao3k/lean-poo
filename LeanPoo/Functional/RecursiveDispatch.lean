import LeanPoo.Functional.RecursiveHandling
import LeanPoo.Functional.DispatchHandling

/-! Adapt existing checked recursive calls to retained-state dispatch methods.
The program index never changes. Every call uses its current registry; cached
source evaluations do not bypass descriptor admission. No evaluator is added. -/
namespace LeanPoo.Functional.RecursiveDispatch
open Prototype Prototype.CallableRecord Prototype.Recursive
variable {program : Self Dynamic.Value} {Ledger E S A : Type}
variable {registry : Dynamic.Registry} {request : CatalogRequest}

structure State (program : Self Dynamic.Value) (Ledger : Type) where
  recursive : RecursiveSession program := {}
  ledger : Ledger
  lastRead : Option Bool := none

inductive Error (program : Self Dynamic.Value) where
  | recursive (failure : RecursiveFailure program)
  | application (message : String)
  deriving Repr

structure Receipt (program : Self Dynamic.Value) (registry : Dynamic.Registry) (request : CatalogRequest) where
  invocation : CatalogInvocation program registry request.slot request.argument
  reused : Option Bool

/-- Heterogeneous dispatch outputs retain each call's exact registry/request. -/
structure Answer (program : Self Dynamic.Value) where
  registry : Dynamic.Registry
  request : CatalogRequest
  receipt : Receipt program registry request

def call (registry : Dynamic.Registry) (request : CatalogRequest) (budget fuel : Nat) :
    EStateM (Error program) (State program Ledger) (Receipt program registry request) := fun state =>
  let result := state.recursive.callSlot registry request.slot request.argument budget fuel
  let next := { state with recursive := result.next, lastRead := result.reused }
  match result.outcome with
  | .error failure => .error (.recursive failure) next
  | .ok invocation => .ok ⟨invocation, result.reused⟩ next

def callPacked (registry : Dynamic.Registry) (request : CatalogRequest) (budget fuel : Nat) :
    EStateM (Error program) (State program Ledger) (Answer program) := do
  let receipt ← call registry request budget fuel
  return ⟨registry, request, receipt⟩

theorem call_ok (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest)
    (budget fuel : Nat) (invocation : CatalogInvocation program registry request.slot request.argument)
    (next : RecursiveSession program) (reused : Option Bool)
    (called : state.recursive.callSlot registry request.slot request.argument budget fuel =
      ⟨.ok invocation, next, reused⟩) :
    (call registry request budget fuel).run state =
      .ok ⟨invocation, reused⟩ { state with recursive := next, lastRead := reused } := by
  simp [call, EStateM.run, called]

theorem call_error (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest)
    (budget fuel : Nat) (failure : RecursiveFailure program) (next : RecursiveSession program) (reused : Option Bool)
    (called : state.recursive.callSlot registry request.slot request.argument budget fuel =
      ⟨.error failure, next, reused⟩) :
    (call registry request budget fuel).run state =
      .error (.recursive failure) { state with recursive := next, lastRead := reused } := by
  simp [call, EStateM.run, called]

def returnedState : EStateM.Result E S A → S
  | .ok _ state => state
  | .error _ state => state

theorem call_state (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest) (budget fuel : Nat) :
    returnedState ((call registry request budget fuel).run state) =
      { state with
        recursive := (state.recursive.callSlot registry request.slot request.argument budget fuel).next
        lastRead := (state.recursive.callSlot registry request.slot request.argument budget fuel).reused } := by
  simp only [call, EStateM.run]
  split <;> rfl

theorem call_ledger (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest) (budget fuel : Nat) :
    (returnedState ((call registry request budget fuel).run state)).ledger = state.ledger := by rw [call_state]

theorem callPacked_state (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest) (budget fuel : Nat) :
    returnedState ((callPacked registry request budget fuel).run state) =
      returnedState ((call registry request budget fuel).run state) := by
  cases observed : (call registry request budget fuel).run state <;>
    simp only [EStateM.run] at observed <;>
    simp [callPacked, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, observed, returnedState]

theorem callPacked_error (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest)
    (budget fuel : Nat) (failure : RecursiveFailure program) (next : RecursiveSession program) (reused : Option Bool)
    (called : state.recursive.callSlot registry request.slot request.argument budget fuel =
      ⟨.error failure, next, reused⟩) :
    (callPacked registry request budget fuel).run state =
      .error (.recursive failure) { state with recursive := next, lastRead := reused } := by
  have failed := call_error state registry request budget fuel failure next reused called
  simp only [EStateM.run] at failed
  simp [callPacked, EStateM.run, bind, EStateM.bind, failed]

theorem callPacked_ok (state : State program Ledger) (registry : Dynamic.Registry) (request : CatalogRequest)
    (budget fuel : Nat) (invocation : CatalogInvocation program registry request.slot request.argument)
    (next : RecursiveSession program) (reused : Option Bool)
    (called : state.recursive.callSlot registry request.slot request.argument budget fuel =
      ⟨.ok invocation, next, reused⟩) :
    (callPacked registry request budget fuel).run state =
      .ok ⟨registry, request, ⟨invocation, reused⟩⟩ { state with recursive := next, lastRead := reused } := by
  have succeeded := call_ok state registry request budget fuel invocation next reused called
  simp only [EStateM.run] at succeeded
  simp [callPacked, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, succeeded]

theorem Receipt.observed (receipt : Receipt program registry request) :
    ∃ depth, solve program depth ⟨request.slot.name, request.argument⟩ = .value receipt.invocation.checked.value :=
  receipt.invocation.observed

theorem Receipt.inputAccepted (receipt : Receipt program registry request) :
    Dynamic.Accepted registry receipt.invocation.signature.input request.argument := receipt.invocation.checked.inputAccepted

theorem Receipt.outputAccepted (receipt : Receipt program registry request) :
    Dynamic.Accepted registry receipt.invocation.signature.output receipt.invocation.checked.value := receipt.invocation.checked.outputAccepted

def Answer.value (answer : Answer program) : Dynamic.Value := answer.receipt.invocation.checked.value

theorem Answer.observed (answer : Answer program) :
    ∃ depth, solve program depth ⟨answer.request.slot.name, answer.request.argument⟩ = .value answer.value :=
  answer.receipt.observed

theorem Answer.outputAccepted (answer : Answer program) :
    Dynamic.Accepted answer.registry answer.receipt.invocation.signature.output answer.value :=
  answer.receipt.outputAccepted

end LeanPoo.Functional.RecursiveDispatch
