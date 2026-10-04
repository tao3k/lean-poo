import LeanPoo.Functional.Requirements

/-! A source-informed interface experiment for Euler budget assembly. The
capabilities correspond to PacketInitializedSpatialBudget fields. Callers
supply the actual context-indexed result types and existing theorem factories;
this file does not import or reprove the upstream analysis. -/
namespace LeanPoo.Examples.ContextualFactories
open C4 Functional

inductive Capability where
  | background | derivative | residual | linear | quadratic
  deriving DecidableEq

universe u v
variable {Context : Type u} {Value : Context → Capability → Type v}

/-- Bind a context at application time; keep its data and proof witnesses in
the same result family. No field is an untyped name-to-value cast. -/
structure Inputs (Context : Type u) (Value : Context → Capability → Type v) where
  background : Factory Context (fun context => Value context .background)
  derivative : Factory Context (fun context => Value context .derivative)
  residual : Factory Context (fun context => Value context .residual)
  linear : Factory Context (fun context => Value context .linear)
  quadratic : Factory Context (fun context => Value context .quadratic)

def graph : Graph := { nodes := [
  { name := "Source" },
  { name := "InitializedFields", parentOrders := [["Source"]] },
  { name := "CorrectionCoefficients", parentOrders := [["Source"]] },
  { name := "SpatialBudget", parentOrders := [["InitializedFields", "CorrectionCoefficients"]] },
  { name := "TightResidual", parentOrders := [["SpatialBudget"]] }] }

def providers (inputs : Inputs Context Value)
    (tightResidual : Factory Context (fun context => Value context .residual)) :
    String → Provider Context Capability Value
  | "InitializedFields", .background => some inputs.background
  | "InitializedFields", .derivative => some inputs.derivative
  | "InitializedFields", .residual => some inputs.residual
  | "CorrectionCoefficients", .linear => some inputs.linear
  | "CorrectionCoefficients", .quadratic => some inputs.quadratic
  | "TightResidual", .residual => some tightResidual
  | _, _ => none

/-- Compile one provider family, then retain it and resolve each capability
once. A selected factory may subsequently serve many compatible contexts. -/
def compileFamily (inputs : Inputs Context Value)
    (tightResidual : Factory Context (fun context => Value context .residual)) :
    Except Error (Provider Context Capability Value) :=
  match linearizeVerified graph "TightResidual" with
  | .error error => .error error
  | .ok order => .ok (assemble order (providers inputs tightResidual))

/-- A consumer declares the capabilities it needs and selects them before
entering its order/time/context loop. Missing capabilities retain their key. -/
abbrev requested : List Capability := [.background, .residual]

abbrev Prepared (Context : Type u) (Value : Context → Capability → Type v) :=
  Requirements.Factories Context Value requested

def prepare (provider : Provider Context Capability Value) :
    Except Capability (Prepared Context Value) := Requirements.prepare provider requested

/-- Invoke the retained functions at one shared context. A real client can
replace this pair projection with its existing budget constructor. -/
def Prepared.build (prepared : Prepared Context Value) :
    Factory Context (fun context => Value context .background × Value context .residual) :=
  fun context =>
    let results := Requirements.build (keys := requested) prepared context
    (results.1, results.2.1)

/-- The full budget checklist uses the same API with heterogeneous field types;
no consumer-specific preparation structure is needed. -/
abbrev budgetRequested : List Capability :=
  [.background, .derivative, .residual, .linear, .quadratic]

example (provider : Provider Context Capability Value) :
    Except Capability (Requirements.Factories Context Value budgetRequested) :=
  Requirements.prepare provider budgetRequested

example (inputs : Inputs Context Value)
    (tight : Factory Context (fun context => Value context .residual)) :
    select ["TightResidual", "SpatialBudget", "InitializedFields", "CorrectionCoefficients", "Source"]
      (providers inputs tight) .residual = some tight := by
  apply select_head
  rfl

example (inputs : Inputs Context Value)
    (tight : Factory Context (fun context => Value context .residual)) :
    select ["TightResidual", "SpatialBudget", "InitializedFields", "CorrectionCoefficients", "Source"]
      (providers inputs tight) .background = some inputs.background := by
  simp [select, providers]

example (provider : Provider Context Capability Value)
    (factory : Factory Context (fun context => Value context .residual))
    (selected : provider .residual = some factory) (context : Context) :
    Functional.apply provider context .residual = some (factory context) := apply_selected selected

#guard (linearizeVerified graph "TightResidual").toOption.map (·.output) ==
  some ["TightResidual", "SpatialBudget", "InitializedFields", "CorrectionCoefficients", "Source"]
#eval IO.println "CONTEXTUAL-FACTORIES-OK"
end LeanPoo.Examples.ContextualFactories
