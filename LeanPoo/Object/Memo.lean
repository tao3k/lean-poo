import LeanPoo.Slots
import LeanPoo.Object.Indexed

namespace LeanPoo.Object

universe u v

/-- Allocate one memoizing thunk per declared slot using the caller's method
resolver. The recursive table ties the final self exactly once. -/
private partial def Plan.buildThunks {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (_plan : Plan Key Value) (keys : List Key)
    (resolve : (key : Key) → Self Key Value → Option (Value key)) :
    Std.DHashMap Key (fun key => Thunk (Option (Value key))) :=
  let rec table : Std.DHashMap Key (fun key => Thunk (Option (Value key))) :=
    keys.foldl (fun current key =>
      current.insert key <| Thunk.mk (fun _ =>
        resolve key (fun nextKey =>
          match table.get? nextKey with
          | some thunk => thunk.get
          | none => none))) {}
  table

/-- Executable object with a shared lazy value cell for each declared key. -/
inductive ResolutionMode where
  | onDemand
  | compiled
  | indexed
  deriving Repr, DecidableEq

structure Memoized (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  plan : Plan Key Value
  thunks : Std.DHashMap Key (fun key => Thunk (Option (Value key)))
  mode : ResolutionMode := .onDemand

/-- Instantiate the C4 plan into a shared call-by-need object. -/
def Plan.memoize {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : Memoized Key Value :=
  ⟨plan, plan.buildThunks (LeanPoo.allSlots plan) plan.resolve, .onDemand⟩

/-- All direct methods in one declaration inherit from the preceding C4
layers. Later duplicate keys replace earlier entries in this declaration. -/
private def Declaration.localMethod {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (inherited : Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key))))
    (key : Key) (spec : SlotPayload Key Value key) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  Prototype.Method.compose spec.toMethod
    ((inherited.get? key).getD Prototype.Method.identity)

private def Declaration.compileLocalMethods {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (declaration : Declaration Key Value)
    (inherited : Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key)))) :
    Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key))) :=
  declaration.slots.foldl (fun methods entry =>
    methods.insert entry.key (Declaration.localMethod inherited entry.key entry.value))
    inherited

private theorem Declaration.compileLocalMethods_get?
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (declaration : Declaration Key Value)
    (inherited : Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key))))
    (key : Key) :
    (declaration.compileLocalMethods inherited).get? key =
    match declaration.slot key with
    | some spec => some (Declaration.localMethod inherited key spec)
    | none => inherited.get? key := by
  unfold Declaration.compileLocalMethods Declaration.slot
  rw [Entry.foldMap_get?_lookup declaration.slots inherited
    (Declaration.localMethod inherited) key]
  cases Entry.lookup declaration.slots key <;> rfl

/-- Compile defaults and effective methods in one least-specific-to-most-
specific traversal, following Gerbil-POO's method-table construction. The
method algebra is still `SlotSpec.toMethod` and `Method.compose`. -/
private def Plan.compileEffective {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (keys : List Key) :
    Std.DHashMap Key (fun key => Self Key Value → Option (Value key)) := Id.run do
  let mut defaults : Std.DHashMap Key Value := {}
  let mut methods : Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key))) := {}
  for name in plan.precedence.reverse do
    if let some declaration := plan.schema.declaration name then
      for entry in declaration.defaults do
        defaults := defaults.insert entry.key entry.value
      methods := declaration.compileLocalMethods methods
  let mut effective : Std.DHashMap Key
      (fun key => Self Key Value → Option (Value key)) := {}
  for key in keys do
    let method := (methods.get? key).getD Prototype.Method.identity
    let base := defaults.get? key
    effective := effective.insert key (fun self => method self (fun _ => base))
  return effective

/-- Precompute every effective method in one pass, then keep slot values
lazy. This favors objects whose callers read many declared slots. -/
def Plan.memoizeCompiled {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : Memoized Key Value :=
  let keys := LeanPoo.allSlots plan
  let effective := plan.compileEffective keys
  let resolve : (key : Key) → Self Key Value → Option (Value key) :=
    fun key self => match effective.get? key with
      | some method => method self
      | none => none
  ⟨plan, plan.buildThunks keys resolve, .compiled⟩

/-- Index direct declarations once and retain lazy slot values. The index's
resolver is proved equal to `Plan.resolve` for every key and open self. -/
def Plan.memoizeIndexed {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : Memoized Key Value :=
  let indexed := plan.index
  ⟨plan, plan.buildThunks (LeanPoo.allSlots plan) indexed.resolve, .indexed⟩

/-- Select how effective methods are built while retaining lazy values. -/
def Plan.memoizeUsing {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (mode : ResolutionMode) : Memoized Key Value :=
  match mode with
  | .onDemand => plan.memoize
  | .compiled => plan.memoizeCompiled
  | .indexed => plan.memoizeIndexed

/-- Rebuild a derived object with the receiver's resolution strategy. -/
def Memoized.rebuild {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (plan : Plan Key Value) :
    Memoized Key Value :=
  plan.memoizeUsing memoized.mode

/-- An executable object can itself be extended: the new object keeps the
source schema and receives a fresh lazy instance. -/
def Memoized.extend {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String)
    (declaration : Declaration Key Value) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.extend memoized.plan.schema name memoized.plan.root declaration
  return memoized.rebuild plan

/-- Compose an executable object with further named parents in its schema. -/
def Memoized.mix {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String)
    (otherParents : List String) (declaration : Declaration Key Value) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.mix memoized.plan.schema name
    (memoized.plan.root :: otherParents) declaration
  return memoized.rebuild plan

inductive CombineError where
  | schema (error : SchemaMergeError)
  | c4 (error : C4.Error)
  deriving Repr

/-- Mix two independently constructed executable objects. Their prototype
graphs must have disjoint node names; the new C4 plan sees both roots. The
left receiver supplies the method-building strategy. -/
def Memoized.mixWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (left right : Memoized Key Value) (name : String)
    (declaration : Declaration Key Value) :
    Except CombineError (Memoized Key Value) := do
  let schema ← (left.plan.schema.mergeDisjoint right.plan.schema).mapError .schema
  let plan ← (LeanPoo.mix schema name [left.plan.root, right.plan.root]
    declaration).mapError .c4
  return left.rebuild plan

/-- Apply an existing override object to this executable base. -/
def Memoized.plus {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name overrideName : String) :
    Except LeanPoo.CompositionError (Memoized Key Value) := do
  let plan : Plan Key Value ←
    LeanPoo.plus memoized.plan.schema name memoized.plan.root overrideName
  return memoized.rebuild plan

/-- Clone this object's direct declaration and replace selected values. -/
def Memoized.clone {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String)
    (overrides : List (Sigma Value)) :
    Except (LeanPoo.CloneError Key) (Memoized Key Value) := do
  let plan : Plan Key Value ←
    LeanPoo.clone memoized.plan.schema name memoized.plan.root overrides
  return memoized.rebuild plan

/-- Revise a declaration without recomputing unchanged C4 topology, then
create a fresh lazy instance. Old objects retain their plan and values. -/
def Memoized.reviseDeclaration {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String)
    (update : Declaration Key Value → Declaration Key Value) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← memoized.plan.reviseDeclaration name update
  return memoized.rebuild plan

/-- Ordered declaration edits share the old C4 order and create just one
fresh lazy instance after all edits have succeeded. -/
def Memoized.reviseDeclarations {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value)
    (updates : List (String × (Declaration Key Value → Declaration Key Value))) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← memoized.plan.reviseDeclarations updates
  return memoized.rebuild plan

/-- Lean's persistent counterpart of changing a direct slot method. -/
def Memoized.reviseSlot {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String) (key : Key)
    (spec : Prototype.SlotSpec (Self Key Value) (Option (Value key))) :
    Except C4.Error (Memoized Key Value) :=
  memoized.reviseDeclaration name (fun declaration => declaration.withSlot key spec)

/-- Lean's persistent counterpart of changing a direct default. -/
def Memoized.reviseDefault {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name : String) (key : Key)
    (value : Value key) : Except C4.Error (Memoized Key Value) :=
  memoized.reviseDeclaration name (fun declaration => declaration.withDefault key value)

/-- Read one slot; forcing a thunk computes its value at most once. -/
def Memoized.read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (key : Key) : Option (Value key) :=
  match memoized.thunks.get? key with
  | some thunk => thunk.get
  | none => none

def Memoized.ref {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (key : Key) :
    Except (LookupError Key) (Value key) :=
  match memoized.read key with
  | some value => .ok value
  | none => .error (.noApplicableMethod key)

/-- A typed missing-slot handler. The handler is evaluated only when the
slot is absent, providing a Lean function counterpart to an object's
custom no-applicable-method behavior. -/
def Memoized.refWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (key : Key)
    (onMissing : (key : Key) → Value key) : Value key :=
  match memoized.read key with
  | some value => value
  | none => onMissing key

/-- Read selected slots through the shared lazy table. -/
def Memoized.select {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (keys : List Key) :
    Except (LookupError Key) (List (Sigma Value)) :=
  LeanPoo.collectValues keys memoized.ref

/-- Traverse every declared slot in object order through the shared lazy
instance. The dependent callback receives each key with its matching type. -/
def Memoized.foldSlots {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (initial : α)
    (step : α → (key : Key) → Value key → α) :
    Except (LookupError Key) α :=
  (LeanPoo.allSlots memoized.plan).foldlM (fun accumulated key => do
    let value ← memoized.ref key
    return step accumulated key value) initial

/-- Force every declared key and materialize typed values in object order. -/
def Memoized.values {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) :
    Except (LookupError Key) (List (Sigma Value)) :=
  memoized.select (LeanPoo.allSlots memoized.plan)

/-- Force every declared slot, retaining the same executable object. -/
def Memoized.force {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) :
    Except (LookupError Key) (Memoized Key Value) := do
  let _ ← memoized.values
  return memoized

/-- Materialize typed values in an explicit key order. -/
def Memoized.valuesSorted {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (lessEq : Key → Key → Bool) :
    Except (LookupError Key) (List (Sigma Value)) :=
  memoized.select (LeanPoo.allSlotsSorted memoized.plan lessEq)

end LeanPoo.Object
