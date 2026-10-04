import LeanPoo.Functional.Requirements

/-! A self-contained five-capability client comparison informed by Euler's
spatial budget fields. Abstract result families preserve the same contracts;
this fixture imports no upstream code and asserts no PDE theorem. -/
namespace LeanPoo.Tests.FunctionalMaintenance
open Functional

inductive Capability where
  | background | derivative | residual | linear | quadratic
  deriving DecidableEq

universe u v
variable {Context : Type u} {Value : Context → Capability → Type v}

-- STUDY-COMMON-BEGIN
abbrev Output (Value : Context → Capability → Type v) (context : Context) :=
  Value context .background × Value context .derivative × Value context .residual ×
    Value context .linear × Value context .quadratic × PUnit
-- STUDY-COMMON-END

-- STUDY-MANUAL-BEGIN
structure Manual (Context : Type u) (Value : Context → Capability → Type v) where
  background : Factory Context (fun c => Value c .background)
  derivative : Factory Context (fun c => Value c .derivative)
  residual : Factory Context (fun c => Value c .residual)
  linear : Factory Context (fun c => Value c .linear)
  quadratic : Factory Context (fun c => Value c .quadratic)

def manualPrepare (provider : Provider Context Capability Value) :
    Except Capability (Manual Context Value) := do
  let background ← require provider .background
  let derivative ← require provider .derivative
  let residual ← require provider .residual
  let linear ← require provider .linear
  let quadratic ← require provider .quadratic
  pure ⟨background, derivative, residual, linear, quadratic⟩

def Manual.build (retained : Manual Context Value) : Factory Context (Output Value) :=
  fun context => (retained.background context, retained.derivative context,
    retained.residual context, retained.linear context, retained.quadratic context, PUnit.unit)
-- STUDY-MANUAL-END

-- STUDY-CHECKLIST-BEGIN
abbrev keys : List Capability :=
  [.background, .derivative, .residual, .linear, .quadratic]
abbrev Checklist (Context : Type u) (Value : Context → Capability → Type v) :=
  Requirements.Factories Context Value keys

def checklistPrepare (provider : Provider Context Capability Value) :
    Except Capability (Checklist Context Value) := Requirements.prepare provider keys

def checklistBuild (retained : Checklist Context Value) : Factory Context (Output Value) :=
  Requirements.build (keys := keys) retained
-- STUDY-CHECKLIST-END

/-- Changing preparation notation preserves successful data/proof-producing
functions and the exact first-missing error, for every typed provider. -/
theorem same_client (provider : Provider Context Capability Value) :
    (checklistPrepare provider).map checklistBuild =
      (manualPrepare provider).map Manual.build := by
  cases background : provider .background <;>
    cases derivative : provider .derivative <;>
    cases residual : provider .residual <;>
    cases linear : provider .linear <;>
    cases quadratic : provider .quadratic <;>
    simp [checklistPrepare, checklistBuild, manualPrepare,
      Requirements.prepare, Requirements.build, require, background,
      derivative, residual, linear, quadratic, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.map] <;> rfl

example (provider other : Provider Context Capability Value)
    (same : ∀ key ∈ keys, other key = provider key) :
    checklistPrepare other = checklistPrepare provider :=
  Requirements.prepare_congr provider other keys same

#print axioms same_client
#print axioms Requirements.prepare_congr
#print axioms Requirements.prepare_rename
#eval IO.println "FUNCTIONAL-MAINTENANCE-OK generic same-client and stable-checklist contracts"
end LeanPoo.Tests.FunctionalMaintenance
