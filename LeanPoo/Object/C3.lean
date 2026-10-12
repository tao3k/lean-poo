import LeanPoo.Object.SlotSyntax
import LeanPoo.Prototype.C3DAG

/-! The paper's C3 topology connected to actual object slot composition. -/
namespace LeanPoo.Object.C3

universe u v
abbrev Graph := Prototype.C3.Graph

structure Schema (Key : Type u) (Value : Key → Type v) where
  graph : Graph
  declaration : String → Option (Declaration Key Value)

structure Plan (Key : Type u) (Value : Key → Type v) where
  schema : Schema Key Value
  root : String
  precedence : List String
  valid : Prototype.C3.linearize schema.graph root = .ok precedence

def compile (schema : Schema Key Value) (root : String) :
    Except LeanPoo.C4.Error (Plan Key Value) :=
  match result : Prototype.C3.linearize schema.graph root with
  | .error error => .error error
  | .ok precedence => .ok ⟨schema, root, precedence, result⟩

def Plan.program (plan : Plan Key Value) : SlotSyntax Key Value :=
  ⟨plan.schema.declaration, plan.precedence⟩

def Plan.resolve (plan : Plan Key Value) (key : Key) (self : Self Key Value) :
    Option (Value key) := plan.program.resolve key self

def Plan.ref (plan : Plan Key Value) (key : Key) (self : Self Key Value) :
    Except (LookupError Key) (Value key) :=
  match plan.resolve key self with
  | none => .error (.noApplicableMethod key)
  | some value => .ok value

/-- Compilation attaches the recursive paper derivation to the order used
by every object slot; no second reference traversal is required. -/
theorem Plan.derivation (plan : Plan Key Value) :
    Prototype.C3.GraphDerivation plan.schema.graph plan.root plan.precedence :=
  Prototype.C3.linearize_derivation _ _ _ plan.valid

/-- Any independent paper derivation yields exactly the object's slot result. -/
theorem Plan.resolve_paper (plan : Plan Key Value) (order : List String)
    (source : Prototype.C3.GraphDerivation plan.schema.graph plan.root order)
    (key : Key) (self : Self Key Value) :
    plan.resolve key self =
      (SlotSyntax.mk plan.schema.declaration order).resolveForward key self := by
  have same := plan.derivation.unique source
  subst order
  exact (plan.program.resolveForward_eq key self).symm

/-- On a DAG, C3 compilation has the complete reference order, including errors. -/
theorem linearize_eq_reference (schema : Schema Key Value)
    (dag : Prototype.C3.DAG schema.graph) (root : String) :
    Prototype.C3.linearize schema.graph root =
      Prototype.C3.linearizeUncached schema.graph root := by
  have same := Prototype.C3.linearizeMany_eq_uncached_dag schema.graph dag [root]
  rw [Prototype.C3.linearizeMany_singleton,
    Prototype.C3.linearizeUncachedMany_singleton] at same
  cases left : Prototype.C3.linearize schema.graph root <;>
    cases right : Prototype.C3.linearizeUncached schema.graph root <;>
    simp_all [Except.map]

unsafe def Plan.instantiate {Key : Type} {Value : Key → Type}
    (plan : Plan Key Value) : Thunk (Self Key Value) := plan.program.instantiate

end LeanPoo.Object.C3

namespace LeanPoo.Object
/-- Public object entry point for the POOF paper's C3 policy. -/
abbrev compileC3 := @C3.compile
end LeanPoo.Object
