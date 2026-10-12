import LeanPoo.Object.Recursive
import LeanPoo.Prototype.CallableRecord

/-! C3 object construction for safe parameterized methods. Method prototypes
use the existing typed composition operation; calls use the existing recursive
machine and its proof-bearing shared cache. -/
namespace LeanPoo.Object.Callable

open Prototype
open Prototype.Recursive
open Prototype.CallableRecord

abbrev Self (Argument : Type) := Prototype.CallableRecord.Self Argument
abbrev Specification (Argument : Type) := Prototype.CallableRecord.Specification Argument

structure Schema (Argument : Type) where
  graph : Prototype.C3.Graph
  declaration : String → Specification Argument
  base : Storage Argument := {}

def Schema.specification (schema : Schema Argument) (precedence : List String) :
    Specification Argument := Prototype.composeAll (precedence.map schema.declaration)

structure Plan (Argument : Type) where
  schema : Schema Argument
  root : String
  precedence : List String
  valid : Prototype.C3.linearize schema.graph root = .ok precedence
  storage : Storage Argument
  built : schema.specification precedence request schema.base = storage

def compile (schema : Schema Argument) (root : String) : Except LeanPoo.C4.Error (Plan Argument) :=
  match valid : Prototype.C3.linearize schema.graph root with
  | .error error => .error error
  | .ok precedence =>
    .ok ⟨schema, root, precedence, valid, schema.specification precedence request schema.base, rfl⟩

def Plan.program (plan : Plan Argument) : Self Argument := generator plan.storage

def Plan.call (plan : Plan Argument) (depth : Nat) (input : Request Argument) :
    Observation Dynamic.Value := solve plan.program depth input

/-- The actual method program agrees with any source C3 graph derivation,
including every parameter, final-self request, error and pending observation. -/
theorem Plan.call_derivation (plan : Plan Argument) (order : List String)
    (derived : Prototype.C3.GraphDerivation plan.schema.graph plan.root order)
    (depth : Nat) (input : Request Argument) :
    plan.call depth input = readPure (plan.schema.specification order request plan.schema.base)
      depth input := by
  have source := Prototype.C3.linearize_derivation _ _ _ plan.valid
  have same := source.unique derived
  subst order
  rw [plan.built]
  rfl

private theorem identityAssembly (order : List String) (self : Self Argument)
    (base : Storage Argument) :
    Prototype.composeAll (order.map fun _ => Prototype.identity) self base = base := by
  induction order with
  | nil => rfl
  | cons _ rest ih =>
    change Prototype.composeAll (rest.map fun _ => Prototype.identity) self base = base
    exact ih

/-- Every existing certified data object can enter the callable protocol.
Its field computations retain their original final-self requests and errors. -/
def Plan.fromFields (plan : Object.Recursive.Plan) (fieldArgument : Argument) : Plan Argument :=
  let schema : Schema Argument :=
    ⟨plan.schema.graph, fun _ => Prototype.identity, ofFields plan.storage fieldArgument⟩
  ⟨schema, plan.root, plan.precedence, plan.valid, ofFields plan.storage fieldArgument,
    identityAssembly plan.precedence request _⟩

theorem Plan.call_fromFields (plan : Object.Recursive.Plan) (fieldArgument : Argument)
    (depth : Nat) (input : Request Argument) :
    (Plan.fromFields plan fieldArgument).call depth input = plan.read depth input.name :=
  readPure_ofFields plan.storage fieldArgument depth input

theorem Plan.call_returns (plan : Plan Argument) (input : Request Argument) (value : Dynamic.Value) :
    (∃ depth, plan.call depth input = .value value) ↔
      Evaluates plan.program (plan.program input) (.value value) :=
  returns_iff_evaluates _ _ _

structure Instance (plan : Plan Argument) where private mk ::
  private cache : Std.Mutex (Cached.Cache plan.program)

variable {Argument : Type} {plan : Plan Argument}

/-- Construction allocates a fresh identity without evaluating any method. -/
def Plan.instantiate (plan : Plan Argument) : IO (Instance plan) := do
  return ⟨← Std.Mutex.new {}⟩

def Instance.callCertified [DecidableEq Argument] (instanceValue : Instance plan)
    (budget : Nat) (input : Request Argument) :
    IO (Except (Cached.Failure plan.program input) (Cached.Receipt plan.program (plan.program input))) :=
  instanceValue.cache.atomically do
    match Cached.runCertified plan.program input budget (← get) with
    | .error failure => return .error failure
    | .ok (receipt, next) =>
      set next
      return .ok receipt

def Instance.call [DecidableEq Argument] (instanceValue : Instance plan)
    (budget : Nat) (input : Request Argument) :
    IO (Except (Cached.Diagnostic (Request Argument)) (Cached.Receipt plan.program (plan.program input))) := do
  return (← instanceValue.callCertified budget input).mapError Cached.Failure.diagnostic

def Instance.cachedRequests (instanceValue : Instance plan) : IO (List (Request Argument)) :=
  instanceValue.cache.atomically do return (← get).entries.map (fun entry => entry.input)

def Instance.statistics (instanceValue : Instance plan) : IO Cached.Statistics :=
  instanceValue.cache.atomically do return (← get).statistics

def Instance.methodNames (_instanceValue : Instance plan) : List String :=
  plan.storage.toList.map Prod.fst

def Plan.mutable (plan : Plan Argument) : IO (Mutable Argument) := create plan.storage

theorem Instance.call_agrees {plan : Plan Argument} {input : Request Argument}
    (receipt : Cached.Receipt plan.program (plan.program input))
    (depth : Nat) (known : plan.call depth input ≠ .pending) :
    plan.call depth input = receipt.result.observation := receipt.agrees depth known

end LeanPoo.Object.Callable
