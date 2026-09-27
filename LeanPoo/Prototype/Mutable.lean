import LeanPoo.Object.Mutable

/-!
The paper's mutable prototype protocol over a single object identity. Lean
uses the existing C4 object and slot evaluator: each layer changes the one
mutable cell, while composition runs the parent before its child.
-/

namespace LeanPoo.Prototype

/-- A declaration-only path retains its C4 witness. A structural extension
stages the schema until the final root is ready for one C4 compilation. -/
inductive PendingPlan (Key : Type) (Value : Key → Type) where
  | valid (plan : Object.Plan Key Value)
  | staged (schema : Object.Schema Key Value) (root : String)

private def PendingPlan.schema : PendingPlan Key Value → Object.Schema Key Value
  | .valid plan => plan.schema
  | .staged schema _ => schema

private def PendingPlan.root : PendingPlan Key Value → String
  | .valid plan => plan.root
  | .staged _ root => root

private def PendingPlan.finish : PendingPlan Key Value →
    Except C4.Error (Object.Plan Key Value)
  | .valid plan => .ok plan
  | .staged schema root => Object.compile schema root

/-- Private construction composes pending edits before allocating an object. -/
inductive PlanPath (Key : Type) (Value : Key → Type) where
  | identity
  | edit (run : PendingPlan Key Value →
      Except C4.Error (PendingPlan Key Value))

private def PlanPath.compose (child parent : PlanPath Key Value) :
    PlanPath Key Value :=
  match child, parent with
  | .identity, path => path
  | path, .identity => path
  | .edit childRun, .edit parentRun =>
      .edit fun pending => do
        let inherited ← parentRun pending
        childRun inherited

/-- An effectful prototype layer receives one mutable object identity.
Its current value represents inherited behavior; later layers rebuild the
same identity with their final self. -/
structure MutableProto (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  apply : Object.Mutable Key Value → IO (Except C4.Error Unit)
  /-- Standard layers stage a private schema and retain validated precedence
  through declaration-only edits. Arbitrary effects use `apply`. -/
  plan? : Option (PlanPath Key Value) := none

def MutableProto.identity {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key] : MutableProto Key Value :=
  ⟨fun _ => pure (.ok ()), some .identity⟩

/-- The parent acts first, then the child acts on that same identity. -/
def MutableProto.compose {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (child parent : MutableProto Key Value) : MutableProto Key Value :=
  { apply := fun object => do
      match ← parent.apply object with
      | .error error => return .error error
      | .ok _ => child.apply object
    plan? := do
      let parentPlan ← parent.plan?
      let childPlan ← child.plan?
      some (PlanPath.compose childPlan parentPlan) }

/-- Compose a most-specific-first list, as for pure prototypes. -/
def MutableProto.composeAll {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layers : List (MutableProto Key Value)) : MutableProto Key Value :=
  layers.foldr MutableProto.compose MutableProto.identity

/-- One named C4 layer using the existing declaration evaluator. -/
def MutableProto.extend {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (declaration : Object.Declaration Key Value) :
    MutableProto Key Value :=
  { apply := fun object => object.extend name declaration
    plan? := some <| .edit fun pending => do
      let next ← LeanPoo.extendSchema pending.schema name pending.root declaration
      return .staged next name }

/-- One named slot increment. `SlotSpec.computed` may request the inherited
method, while `SlotSpec.self` reads the final composed object. -/
def MutableProto.slot {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (key : Key)
    (spec : SlotSpec (Object.Self Key Value) (Option (Value key))) :
    MutableProto Key Value :=
  MutableProto.extend name (Object.Declaration.empty.withSlot key spec)

/-- Revise an existing node of the current object without changing C4
topology. This can be composed with extension layers. -/
def MutableProto.revise {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String)
    (update : Object.Declaration Key Value → Object.Declaration Key Value) :
    MutableProto Key Value :=
  { apply := fun object => object.reviseDeclaration name update
    plan? := some <| .edit fun pending =>
      match pending with
      | .valid plan => (plan.reviseDeclaration name update).map .valid
      | .staged schema root =>
          (schema.reviseDeclaration name update).map (fun next => .staged next root) }

/-- Build a private identity and return it only on success. Standard layers
compile C4 only after the staged structure is complete; arbitrary
effect layers run sequentially on a private cell. -/
def MutableProto.instantiate {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prototype : MutableProto Key Value)
    (base : Object.Memoized Key Value) :
    IO (Except C4.Error (Object.Mutable Key Value)) := do
  match prototype.plan? with
  | some .identity => return .ok (← Object.Mutable.new base)
  | some (.edit stage) =>
      match stage (.valid base.plan) with
      | .error error => return .error error
      | .ok pending =>
          match pending.finish with
          | .error error => return .error error
          | .ok final => return .ok (← Object.Mutable.new (base.rebuild final))
  | none =>
    let object ← Object.Mutable.new base
    match ← prototype.apply object with
    | .error error => return .error error
    | .ok _ => return .ok object

/-- Build the same identity with its final effective method table compiled
once. The object remains private until the whole prototype succeeds. -/
def MutableProto.instantiateCompiled {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prototype : MutableProto Key Value)
    (base : Object.Memoized Key Value) :
    IO (Except C4.Error (Object.Mutable Key Value)) := do
  match prototype.plan? with
  | some .identity => return .ok (← Object.Mutable.new base.plan.memoizeCompiled)
  | some (.edit stage) =>
      match stage (.valid base.plan) with
      | .error error => return .error error
      | .ok pending =>
          match pending.finish with
          | .error error => return .error error
          | .ok final => return .ok (← Object.Mutable.new final.memoizeCompiled)
  | none =>
      match ← prototype.instantiate base with
      | .error error => return .error error
      | .ok object =>
          let final ← object.snapshot
          object.cell.set final.plan.memoizeCompiled
          return .ok object

end LeanPoo.Prototype
