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

private abbrev CompiledTables {Key : Type u} {Value : Key → Type v}
    [BEq Key] [Hashable Key] :=
  Std.DHashMap Key Value ×
    Std.DHashMap Key
      (fun key => Prototype.Method (Self Key Value) (Option (Value key)))

/-- A single C4 traversal builds defaults and methods together. -/
private def compileTablesFor {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (names : List String) :
    CompiledTables (Key := Key) (Value := Value) :=
  names.foldl (fun tables name =>
    match schema.declaration name with
    | none => tables
    | some declaration =>
        (declaration.defaults.foldl (fun defaults entry =>
          defaults.insert entry.key entry.value) tables.1,
         declaration.compileLocalMethods tables.2)) ({}, {})

/-- The compiled base is the last default on the parent-first C4 path. -/
private theorem compileTablesFor_default_get?
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (names : List String) (key : Key) :
    (compileTablesFor schema names).1.get? key =
    names.foldl (fun inherited name =>
      match schema.declaration name with
      | none => inherited
      | some declaration =>
          match declaration.default key with
          | none => inherited
          | some value => some value) none := by
  unfold compileTablesFor
  have go (rest : List String) (tables : CompiledTables (Key := Key) (Value := Value)) :
      (rest.foldl (fun tables name =>
        match schema.declaration name with
        | none => tables
        | some declaration =>
            (declaration.defaults.foldl (fun defaults entry =>
              defaults.insert entry.key entry.value) tables.1,
             declaration.compileLocalMethods tables.2)) tables).1.get? key =
      rest.foldl (fun inherited name =>
        match schema.declaration name with
        | none => inherited
        | some declaration =>
            match declaration.default key with
            | none => inherited
            | some value => some value) (tables.1.get? key) := by
    induction rest generalizing tables with
    | nil => rfl
    | cons name tail ih =>
        simp only [List.foldl_cons]
        rw [ih]
        cases schema.declaration name with
        | none => rfl
        | some declaration =>
            simp only
            rw [Entry.foldMap_get?_lookup declaration.defaults tables.1
              (fun _ value => value) key]
            unfold Declaration.default
            cases Entry.lookup declaration.defaults key <;> rfl
  simpa using go names ({}, {})

/-- The compiled method for any key is the parent-first C4 composition,
including keys with no direct method in a given declaration. -/
private theorem compileTablesFor_method_getD
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (names : List String) (key : Key) :
    ((compileTablesFor schema names).2.get? key).getD
      Prototype.Method.identity =
    names.foldl (fun inherited name =>
      match schema.declaration name with
      | none => inherited
      | some declaration =>
          match declaration.slot key with
          | none => inherited
          | some spec => Prototype.Method.compose spec.toMethod inherited)
      Prototype.Method.identity := by
  unfold compileTablesFor
  have go (rest : List String) (tables : CompiledTables (Key := Key) (Value := Value)) :
      ((rest.foldl (fun tables name =>
        match schema.declaration name with
        | none => tables
        | some declaration =>
            (declaration.defaults.foldl (fun defaults entry =>
              defaults.insert entry.key entry.value) tables.1,
             declaration.compileLocalMethods tables.2)) tables).2.get? key).getD
        Prototype.Method.identity =
      rest.foldl (fun inherited name =>
        match schema.declaration name with
        | none => inherited
        | some declaration =>
            match declaration.slot key with
            | none => inherited
            | some spec => Prototype.Method.compose spec.toMethod inherited)
        ((tables.2.get? key).getD Prototype.Method.identity) := by
    induction rest generalizing tables with
    | nil => rfl
    | cons name tail ih =>
        simp only [List.foldl_cons]
        rw [ih]
        cases found : schema.declaration name with
        | none => simp
        | some declaration =>
            simp only
            rw [Declaration.compileLocalMethods_get?]
            cases declaration.slot key <;> rfl
  simpa using go names ({}, {})

/-- The compiled tables give the same open-recursive result as the canonical
resolver for every key, before the final finite-key projection. -/
private theorem Plan.compiledTables_resolve
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (key : Key) (self : Self Key Value) :
    let tables := compileTablesFor plan.schema plan.precedence.reverse
    ((tables.2.get? key).getD Prototype.Method.identity) self
      (fun _ => tables.1.get? key) = plan.resolve key self := by
  simp only
  rw [compileTablesFor_method_getD, compileTablesFor_default_get?]
  rfl

private theorem foldInsert_preserve {Key : Type u} {Result : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (keys : List Key) (table : Std.DHashMap Key Result)
    (f : (key : Key) → Result key) (key : Key)
    (present : table.get? key = some (f key)) :
    (keys.foldl (fun current next => current.insert next (f next)) table).get? key =
      some (f key) := by
  induction keys generalizing table with
  | nil => exact present
  | cons next rest ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [Std.DHashMap.get?_insert]
      by_cases same : key = next
      · subst next
        simp
      · have reverse : next ≠ key := by intro h; exact same h.symm
        simpa [reverse, same] using present

private theorem foldInsert_mem {Key : Type u} {Result : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (keys : List Key) (table : Std.DHashMap Key Result)
    (f : (key : Key) → Result key) (key : Key)
    (member : key ∈ keys) :
    (keys.foldl (fun current next => current.insert next (f next)) table).get? key =
      some (f key) := by
  induction keys generalizing table with
  | nil => cases member
  | cons next rest ih =>
      simp only [List.foldl_cons]
      by_cases same : key = next
      · subst next
        apply foldInsert_preserve
        simp
      · have tailMember : key ∈ rest := by
          simpa [same] using member
        exact ih (table.insert next (f next)) tailMember

/-- Compile defaults and effective methods in one least-specific-to-most-
specific traversal, following Gerbil-POO's method-table construction. The
method algebra is still `SlotSpec.toMethod` and `Method.compose`. -/
private def Plan.compileEffective {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (keys : List Key) :
    Std.DHashMap Key (fun key => Self Key Value → Option (Value key)) :=
  let (defaults, methods) := compileTablesFor plan.schema plan.precedence.reverse
  keys.foldl (fun effective key =>
    let method := (methods.get? key).getD Prototype.Method.identity
    let base := defaults.get? key
    effective.insert key (fun self => method self (fun _ => base))) {}

/-- Every materialized key in the compiled table resolves exactly as the
canonical C4 plan, for any open-recursive self. -/
private theorem Plan.compileEffective_get?_mem
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (keys : List Key) (key : Key)
    (member : key ∈ keys) :
    (plan.compileEffective keys).get? key = some (plan.resolve key) := by
  let tables := compileTablesFor plan.schema plan.precedence.reverse
  have lookup : (plan.compileEffective keys).get? key =
      some (fun self =>
        ((tables.2.get? key).getD Prototype.Method.identity) self
          (fun _ => tables.1.get? key)) := by
    unfold Plan.compileEffective
    exact foldInsert_mem keys
      ({} : Std.DHashMap Key (fun key => Self Key Value → Option (Value key)))
      (fun key self =>
        ((tables.2.get? key).getD Prototype.Method.identity) self
          (fun _ => tables.1.get? key)) key member
  rw [lookup]
  congr 1
  funext self
  exact plan.compiledTables_resolve key self

/-- A reusable, proof-backed method table for one validated C4 plan. The
compiled functions remain open in `self`; only instances allocate lazy cells. -/
structure CompiledPlan (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  plan : Plan Key Value
  keys : List Key
  effective : Std.DHashMap Key (fun key => Self Key Value → Option (Value key))
  sound : ∀ key, key ∈ keys → effective.get? key = some (plan.resolve key)

/-- Stage C4 method composition once for any number of later instances. -/
def Plan.compileMemo {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : CompiledPlan Key Value :=
  let keys := LeanPoo.allSlots plan
  { plan
    keys
    effective := plan.compileEffective keys
    sound := plan.compileEffective_get?_mem keys }

/-- Read a compiled open method. Unmaterialized keys have no method. -/
def CompiledPlan.resolve {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (compiled : CompiledPlan Key Value) (key : Key) (self : Self Key Value) :
    Option (Value key) :=
  match compiled.effective.get? key with
  | some method => method self
  | none => none

/-- Every materialized compiled method has the plan's open-recursive meaning. -/
theorem CompiledPlan.resolve_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (compiled : CompiledPlan Key Value) (key : Key)
    (member : key ∈ compiled.keys) (self : Self Key Value) :
    compiled.resolve key self = compiled.plan.resolve key self := by
  simp [CompiledPlan.resolve, compiled.sound key member]

/-- Tie a fresh lazy self table while reusing the compiled open methods. -/
def CompiledPlan.instantiate {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (compiled : CompiledPlan Key Value) : Memoized Key Value :=
  ⟨compiled.plan,
    compiled.plan.buildThunks compiled.keys compiled.resolve, .compiled⟩

/-- Precompute every effective method in one pass, then keep slot values
lazy. This favors objects whose callers read many declared slots. -/
def Plan.memoizeCompiled {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : Memoized Key Value :=
  plan.compileMemo.instantiate

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

theorem Memoized.rebuild_plan {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (plan : Plan Key Value) :
    (memoized.rebuild plan).plan = plan := by
  cases memoized with
  | mk current thunks mode =>
      cases mode <;> rfl

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

/-- Mix first-class executable objects from disjoint C4 families. Their
prototype graphs must have disjoint node names. The receiver comes first in
the parent order and supplies the method-building strategy. -/
def Memoized.mixMany {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (first : Memoized Key Value) (others : List (Memoized Key Value))
    (name : String)
    (declaration : Declaration Key Value) :
    Except CombineError (Memoized Key Value) := do
  let schema ← others.foldlM (fun schema other =>
    (schema.mergeDisjoint other.plan.schema).mapError .schema) first.plan.schema
  let parents := first.plan.root :: others.map (·.plan.root)
  let plan ← (LeanPoo.mix schema name parents
    declaration).mapError .c4
  return first.rebuild plan

/-- Mix two independently constructed executable objects. The left receiver
supplies the method-building strategy. -/
def Memoized.mixWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (left right : Memoized Key Value) (name : String)
    (declaration : Declaration Key Value) :
    Except CombineError (Memoized Key Value) :=
  left.mixMany [right] name declaration

/-- Apply an existing override object to this executable base. -/
def Memoized.plus {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (memoized : Memoized Key Value) (name overrideName : String) :
    Except LeanPoo.CompositionError (Memoized Key Value) := do
  let plan : Plan Key Value ←
    LeanPoo.plus memoized.plan.schema name memoized.plan.root overrideName
  return memoized.rebuild plan

inductive PlusWithError where
  | schema (error : SchemaMergeError)
  | composition (error : LeanPoo.CompositionError)
  deriving Repr

/-- Apply an independent first-class override object using Gerbil's `.+`
topology: copy its direct declaration and place its parents before the base.
The two object families must have disjoint node names. -/
def Memoized.plusWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (base override : Memoized Key Value) (name : String) :
    Except PlusWithError (Memoized Key Value) := do
  let schema ← (base.plan.schema.mergeDisjoint override.plan.schema).mapError .schema
  let plan ← (LeanPoo.plus schema name base.plan.root override.plan.root).mapError
    .composition
  return base.rebuild plan

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
