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

/-- The editable part of one prototype identity: its direct methods and
the C4 metadata that positions them in the object. The name is fixed by the
focus, so a specification edit cannot silently rename another prototype. -/
structure Specification (Key : Type u) (Value : Key → Type v) where
  declaration : Declaration Key Value
  parentOrders : List (List String)
  suffix : Bool

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

/-- Revise a complete prototype specification. A direct-method-only edit
reuses the certified precedence; a parent or suffix edit is recompiled by C4.
The original plan remains available when recompilation fails. -/
def Plan.reviseSpecification (plan : Plan Key Value) (name : String)
    (specification : Specification Key Value) :
    Except C4.Error (Plan Key Value) := do
  let some node := plan.schema.graph.findNode? name |
    throw (.unknownNode name)
  if node.parentOrders == specification.parentOrders &&
      node.suffix == specification.suffix then
    plan.reviseDeclaration name (fun _ => specification.declaration)
  else
    let revised ← plan.schema.reviseDeclaration name
      (fun _ => specification.declaration)
    let nodes := revised.graph.nodes.map fun current =>
      if current.name == name then
        { current with
          parentOrders := specification.parentOrders
          suffix := specification.suffix }
      else current
    compile { revised with graph := { nodes } } plan.root

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

/-- Scan defaults from the least specific declaration toward the root. -/
private def baseDefaultForward (schema : Schema Key Value)
    (order : List String) (key : Key) : Option (Value key) :=
  order.reverse.foldl (fun inherited name =>
    match schema.declaration name with
    | none => inherited
    | some declaration =>
      match declaration.default key with
      | none => inherited
      | some value => some value) none

private theorem baseDefaultForward_eq (schema : Schema Key Value)
    (order : List String) (key : Key) :
    baseDefaultForward schema order key = baseDefault schema order key := by
  unfold baseDefaultForward baseDefault
  rw [List.foldl_reverse]

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

/-- One default layer in the canonical least-to-most-specific evaluation. -/
def Schema.defaultStep (schema : Schema Key Value) (key : Key)
    (name : String) (inherited : Option (Value key)) : Option (Value key) :=
  match schema.declaration name with
  | none => inherited
  | some declaration => match declaration.default key with
    | none => inherited
    | some value => some value

/-- One delayed method layer in the canonical C4 evaluation. -/
def Schema.methodStep (schema : Schema Key Value) (key : Key)
    (name : String) (inherited : Prototype.Method (Self Key Value) (Option (Value key))) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  match schema.declaration name with
  | none => inherited
  | some declaration => match declaration.slot key with
    | none => inherited
    | some spec => Prototype.Method.compose spec.toMethod inherited

/-- Expose the canonical method/default fold for semantic transformations. -/
theorem Plan.compileSlot_apply (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) :
    plan.compileSlot key self =
      (plan.precedence.foldr (plan.schema.methodStep key) Prototype.Method.identity)
        self (fun _ => plan.precedence.foldr (plan.schema.defaultStep key) none) := by
  unfold Plan.compileSlot Schema.methodStep Schema.defaultStep baseDefault
  rfl

/-- The paper's parent-first construction of one effective slot method. -/
def Plan.compileSlotForward (plan : Plan Key Value) (key : Key) :
    Self Key Value → Option (Value key) :=
  let default := baseDefaultForward plan.schema plan.precedence key
  let methods : Prototype.Method (Self Key Value) (Option (Value key)) :=
    plan.precedence.reverse.foldl (fun inherited name =>
      match plan.schema.declaration name with
      | none => inherited
      | some declaration =>
        match declaration.slot key with
        | none => inherited
        | some spec => Prototype.Method.compose spec.toMethod inherited)
      Prototype.Method.identity
  fun self => methods self (fun _ => default)

/-- Parent-first accumulation has exactly the original C4 slot meaning. -/
theorem Plan.compileSlotForward_eq (plan : Plan Key Value) (key : Key) :
    plan.compileSlotForward key = plan.compileSlot key := by
  unfold Plan.compileSlotForward Plan.compileSlot
  rw [baseDefaultForward_eq]
  rw [List.foldl_reverse]

/-- Resolve one typed slot with an explicit open-recursive self. -/
def Plan.resolve (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) : Option (Value key) :=
  plan.compileSlotForward key self

/-- The parent-first resolver agrees with the original C4 fold for every
key and open-recursive self, including keys absent from all declarations. -/
theorem Plan.resolve_eq_compileSlot (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) :
    plan.resolve key self = plan.compileSlot key self := by
  unfold Plan.resolve
  rw [plan.compileSlotForward_eq]

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
