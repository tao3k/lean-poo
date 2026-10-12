import LeanPoo.Object.C3
import LeanPoo.Prototype.MutableRecord

/-! A safe, executable POOF object path joining C3, prototype composition,
dynamic values and the operational semantics of final-self recursion. -/
namespace LeanPoo.Object.Recursive

open Prototype
open Prototype.Recursive
open Prototype.MutableRecord
abbrev Specification := Prototype.MutableRecord.Specification

structure Schema where
  graph : Prototype.C3.Graph
  declaration : String → Specification
  base : Storage := {}

def Schema.specification (schema : Schema) (precedence : List String) : Specification :=
  Specification.composeAll (precedence.map schema.declaration)

structure Plan where
  schema : Schema
  root : String
  precedence : List String
  valid : Prototype.C3.linearize schema.graph root = .ok precedence
  storage : Storage
  built : (schema.specification precedence).transition schema.base = (storage, .ok ())

inductive Error where
  | topology (error : LeanPoo.C4.Error)
  | prototype (message : String)
  deriving Repr

def compile (schema : Schema) (root : String) : Except Error Plan :=
  match order : Prototype.C3.linearize schema.graph root with
  | .error error => .error (.topology error)
  | .ok precedence =>
    match built : (schema.specification precedence).transition schema.base with
    | (_storage, .error message) => .error (.prototype message)
    | (storage, .ok ()) => .ok ⟨schema, root, precedence, order, storage, built⟩

def Plan.read (plan : Plan) (depth : Nat) (key : String) : Observation Dynamic.Value :=
  readPure plan.storage depth key

/-- The actual closed object observation agrees with any recursive paper C3
derivation, for every depth and key, including error and pending outcomes. -/
theorem Plan.read_derivation (plan : Plan) (order : List String)
    (derived : Prototype.C3.GraphDerivation plan.schema.graph plan.root order)
    (depth : Nat) (key : String) :
    plan.read depth key =
      readPure ((plan.schema.specification order).transition plan.schema.base).1 depth key := by
  have source := Prototype.C3.linearize_derivation _ _ _ plan.valid
  have same := source.unique derived
  subst order
  rw [plan.built]
  rfl

/-- Completed object reads are exactly unbounded operational evaluations. -/
theorem Plan.read_returns (plan : Plan) (key : String) (value : Dynamic.Value) :
    (∃ depth, plan.read depth key = .value value) ↔
      Evaluates (generator plan.storage) (generator plan.storage key) (.value value) :=
  read_returns_iff _ _ _

theorem Plan.read_diverges (plan : Plan) (key : String) :
    (∀ depth, plan.read depth key = .pending) ↔
      ∀ result, ¬Evaluates (generator plan.storage) (generator plan.storage key) result :=
  diverges_iff_no_evaluation _ _

/-- A mutable instance starts from the exact certified pure storage and a
fresh hash identity. Later mutations are visible through every mutable alias. -/
def Plan.mutable (plan : Plan) : IO Mutable := create plan.storage

end LeanPoo.Object.Recursive
