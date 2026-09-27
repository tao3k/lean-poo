import LeanPoo.Object.Schema

/-!
The evaluation order follows Gerbil-POO object.ss: defaults first, then
methods from least to most specific C4 prototype. The inherited computation
is kept as a thunk so an overriding method can leave it unevaluated.
-/

namespace LeanPoo.Object

universe u v

/-- A validated precedence order can be shared by many slot lookups. -/
structure Plan (Key : Type u) (Value : Key → Type v) where
  schema : Schema Key Value
  root : String
  precedence : List String
  valid : C4.linearize schema.graph root = .ok precedence

/-- The required-lookup boundary corresponding to object.ss .ref. -/
inductive LookupError (Key : Type u) where
  | noApplicableMethod (key : Key)
  deriving Repr

/-- Compile C4 topology once, as object.ss does during instantiation. -/
def compile (schema : Schema Key Value) (root : String) :
    Except C4.Error (Plan Key Value) :=
  match result : C4.linearize schema.graph root with
  | .error error => .error error
  | .ok precedence => .ok ⟨schema, root, precedence, result⟩

/-- Change a declaration while retaining the validated C4 order. The graph
and root are unchanged, so no second linearization is needed. -/
def Plan.reviseDeclaration (plan : Plan Key Value) (name : String)
    (update : Declaration Key Value → Declaration Key Value) :
    Except C4.Error (Plan Key Value) :=
  match result : plan.schema.reviseDeclaration name update with
  | .error error => .error error
  | .ok revised =>
      have sameGraph : revised.graph = plan.schema.graph := by
        unfold Schema.reviseDeclaration at result
        split at result
        · contradiction
        · cases result
          rfl
      .ok {
        schema := revised
        root := plan.root
        precedence := plan.precedence
        valid := by
          rw [sameGraph]
          exact plan.valid
      }

/-- Apply ordered declaration edits to one plan. Every intermediate edit
retains the same validated topology; callers instantiate only the final plan. -/
def Plan.reviseDeclarations (plan : Plan Key Value)
    (updates : List (String × (Declaration Key Value → Declaration Key Value))) :
    Except C4.Error (Plan Key Value) :=
  updates.foldlM (fun current (name, update) =>
    current.reviseDeclaration name update) plan

theorem Plan.reviseDeclaration_preserves_precedence
    (plan : Plan Key Value) (name : String)
    (update : Declaration Key Value → Declaration Key Value)
    (revised : Plan Key Value)
    (result : plan.reviseDeclaration name update = .ok revised) :
    revised.precedence = plan.precedence := by
  unfold Plan.reviseDeclaration at result
  split at result
  · cases result
  · cases result
    rfl

/-- The most specific declared default is the base for method composition. -/
private def baseDefault (schema : Schema Key Value) (order : List String)
    (key : Key) : Option (Value key) :=
  order.foldr (fun name inherited =>
    match schema.declaration name with
    | none => inherited
    | some declaration =>
      match declaration.default key with
      | none => inherited
      | some value => some value) none

/-- Assemble one inherited slot function, keeping self open until lookup. -/
def Plan.compileSlot (plan : Plan Key Value) (key : Key) :
    Self Key Value → Option (Value key) :=
  let default := baseDefault plan.schema plan.precedence key
  let methods : Prototype.Method (Self Key Value) (Option (Value key)) :=
    plan.precedence.foldr (fun name inherited =>
      match plan.schema.declaration name with
      | none => inherited
      | some declaration =>
        match declaration.slot key with
        | none => inherited
        | some spec => Prototype.Method.compose spec.toMethod inherited)
      Prototype.Method.identity
  fun self => methods self (fun _ => default)

/-- Resolve one typed slot with an explicit open-recursive self. -/
def Plan.resolve (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) : Option (Value key) :=
  plan.compileSlot key self

/-- Require a resolved slot; optional probing remains available via resolve. -/
def Plan.ref (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) : Except (LookupError Key) (Value key) :=
  match plan.resolve key self with
  | some value => .ok value
  | none => .error (.noApplicableMethod key)

/-- A convenience entry point for a single lookup. Reuse a compiled Plan
when resolving several slots of the same object. -/
def resolve (schema : Schema Key Value) (root : String) (key : Key)
    (self : Self Key Value) : Except C4.Error (Option (Value key)) := do
  let plan ← compile schema root
  return plan.resolve key self

/-- Reusing a compiled plan preserves the single-lookup meaning. -/
theorem resolve_compiled (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) :
    resolve plan.schema plan.root key self = .ok (plan.resolve key self) := by
  unfold resolve compile
  split
  · rename_i error result
    have impossible := plan.valid.symm.trans result
    cases impossible
  · rename_i precedence result
    have same : precedence = plan.precedence := by
      injection plan.valid.symm.trans result with equality
      exact equality.symm
    subst precedence
    rfl

end LeanPoo.Object
