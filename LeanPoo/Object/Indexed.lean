import LeanPoo.Object.Resolve

/-!
Index each declaration once, then resolve slots through constant-time typed
lookups in C4 order. The index is an implementation of the existing resolver,
not a second source of slot semantics.
-/

namespace LeanPoo.Object

universe u v

structure IndexedLayer (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  defaults : Std.DHashMap Key Value
  slots : Std.DHashMap Key (SlotPayload Key Value)

def IndexedLayer.ofDeclaration {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (declaration : Declaration Key Value) :
    IndexedLayer Key Value :=
  ⟨Entry.toMap declaration.defaults, Entry.toMap declaration.slots⟩

structure IndexedPlan (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  plan : Plan Key Value
  layers : List (Option (IndexedLayer Key Value))
  aligned : layers = plan.precedence.reverse.map (fun name =>
    (plan.schema.declaration name).map IndexedLayer.ofDeclaration)

def Plan.index {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] (plan : Plan Key Value) :
    IndexedPlan Key Value :=
  ⟨plan, plan.precedence.reverse.map (fun name =>
    (plan.schema.declaration name).map IndexedLayer.ofDeclaration), rfl⟩

private def IndexedLayer.defaultStep {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) (inherited : Option (Value key))
    (layer : Option (IndexedLayer Key Value)) : Option (Value key) :=
  match layer with
  | none => inherited
  | some layer =>
      match layer.defaults.get? key with
      | none => inherited
      | some value => some value

private def IndexedLayer.methodStep {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key)
    (inherited : Prototype.Method (Self Key Value) (Option (Value key)))
    (layer : Option (IndexedLayer Key Value)) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  match layer with
  | none => inherited
  | some layer =>
      match layer.slots.get? key with
      | none => inherited
      | some spec => Prototype.Method.compose spec.toMethod inherited

private theorem IndexedLayer.defaultStep_ofDeclaration
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) (inherited : Option (Value key))
    (declaration : Option (Declaration Key Value)) :
    IndexedLayer.defaultStep key inherited
      (declaration.map IndexedLayer.ofDeclaration) =
    match declaration with
    | none => inherited
    | some declaration =>
        match declaration.default key with
        | none => inherited
        | some value => some value := by
  cases declaration with
  | none => rfl
  | some declaration =>
      simp [IndexedLayer.defaultStep, IndexedLayer.ofDeclaration,
        Declaration.default, Entry.toMap_get?]

private theorem IndexedLayer.methodStep_ofDeclaration
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key)
    (inherited : Prototype.Method (Self Key Value) (Option (Value key)))
    (declaration : Option (Declaration Key Value)) :
    IndexedLayer.methodStep key inherited
      (declaration.map IndexedLayer.ofDeclaration) =
    match declaration with
    | none => inherited
    | some declaration =>
        match declaration.slot key with
        | none => inherited
        | some spec => Prototype.Method.compose spec.toMethod inherited := by
  cases declaration with
  | none => rfl
  | some declaration =>
      simp [IndexedLayer.methodStep, IndexedLayer.ofDeclaration,
        Declaration.slot, Entry.toMap_get?]
      rfl

def IndexedPlan.resolve {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value)
    (key : Key) (self : Self Key Value) : Option (Value key) :=
  let default := indexed.layers.foldl (IndexedLayer.defaultStep key) none
  let method := indexed.layers.foldl (IndexedLayer.methodStep key)
    Prototype.Method.identity
  method self (fun _ => default)

theorem IndexedPlan.resolve_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key)
    (self : Self Key Value) :
    indexed.resolve key self = indexed.plan.resolve key self := by
  unfold IndexedPlan.resolve Plan.resolve Plan.compileSlotForward
  rw [indexed.aligned]
  simp only [List.foldl_map, IndexedLayer.defaultStep_ofDeclaration,
    IndexedLayer.methodStep_ofDeclaration]
  rfl

theorem Plan.index_resolve_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (key : Key) (self : Self Key Value) :
    (plan.index).resolve key self = plan.resolve key self :=
  (plan.index).resolve_sound key self

/-- One key's actual defaults and method payloads in the admitted C4 order.
This projection retains payload identity; matching names alone is insufficient.
The typed declarations are already admitted. Native metadata hooks, mutable
raw exposure and preparation failures require their own issuer/fallback. -/
def IndexedLayer.projectKey {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) (layer : Option (IndexedLayer Key Value)) :
    Option (Value key) × Option (SlotPayload Key Value key) :=
  match layer with
  | none => (none, none)
  | some layer => (layer.defaults.get? key, layer.slots.get? key)

/-- A concrete edit to another method cannot change this key's recipe. -/
theorem IndexedLayer.projectKey_other_slot {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layer : IndexedLayer Key Value) (key changed : Key)
    (spec : SlotPayload Key Value changed) (other : changed ≠ key) :
    projectKey key (some { layer with slots := layer.slots.insert changed spec }) =
      projectKey key (some layer) := by
  simp [projectKey, Std.DHashMap.get?_insert, other]

/-- Defaults and direct methods retain their separate namespaces. -/
theorem IndexedLayer.projectKey_other_default {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layer : IndexedLayer Key Value) (key changed : Key)
    (value : Value changed) (other : changed ≠ key) :
    projectKey key (some { layer with defaults := layer.defaults.insert changed value }) =
      projectKey key (some layer) := by
  simp [projectKey, Std.DHashMap.get?_insert, other]

private def projectedDefault {Key : Type u} {Value : Key → Type v} {key : Key}
    (inherited : Option (Value key))
    (entry : Option (Value key) × Option (SlotPayload Key Value key)) : Option (Value key) :=
  entry.1.or inherited

private def projectedMethod {Key : Type u} {Value : Key → Type v} {key : Key}
    (inherited : Prototype.Method (Self Key Value) (Option (Value key)))
    (entry : Option (Value key) × Option (SlotPayload Key Value key)) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  match entry.2 with
  | none => inherited
  | some spec => spec.withParent inherited

/-- Prepare the key's unbound method, then supply the invocation's final self.
This is the original two-pass default/method composition. It neither invokes
slot bodies during preparation nor retains a receiver's computed value. -/
def prepareProjectedKey {Key : Type u} {Value : Key → Type v} {key : Key}
    (entries : List (Option (Value key) × Option (SlotPayload Key Value key))) :
    Self Key Value → Option (Value key) :=
  let inherited := entries.foldl projectedDefault none
  let method := entries.foldl projectedMethod Prototype.Method.identity
  fun self => method self (fun _ => inherited)

def IndexedPlan.keyProjection {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key) :=
  indexed.layers.map (IndexedLayer.projectKey key)

def IndexedPlan.prepareKey {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key) : Self Key Value → Option (Value key) :=
  prepareProjectedKey (indexed.keyProjection key)

theorem IndexedPlan.prepareKey_eq_resolve {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key) (self : Self Key Value) :
    indexed.prepareKey key self = indexed.resolve key self := by
  have defaults (entry : Option (IndexedLayer Key Value)) (old : Option (Value key)) :
      projectedDefault old (IndexedLayer.projectKey key entry) =
        IndexedLayer.defaultStep key old entry := by
    cases entry with
    | none => rfl
    | some layer =>
      cases found : layer.defaults.get? key <;>
        simp [projectedDefault, IndexedLayer.projectKey, IndexedLayer.defaultStep, found]
  have methods (entry : Option (IndexedLayer Key Value))
      (old : Prototype.Method (Self Key Value) (Option (Value key))) :
      projectedMethod old (IndexedLayer.projectKey key entry) =
        IndexedLayer.methodStep key old entry := by
    cases entry with
    | none => rfl
    | some layer =>
      cases found : layer.slots.get? key <;>
        simp [projectedMethod, IndexedLayer.projectKey, IndexedLayer.methodStep,
          found, Prototype.SlotSpec.withParent_eq]
  simp only [IndexedPlan.prepareKey, IndexedPlan.keyProjection, prepareProjectedKey,
    List.foldl_map, defaults, methods, IndexedPlan.resolve]

/-- The same prepared recipe works for every final receiver, retaining its
inherited continuation and the original resolver's missing/value behavior. -/
theorem IndexedPlan.prepareKey_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key) (self : Self Key Value) :
    indexed.prepareKey key self = indexed.plan.resolve key self :=
  (indexed.prepareKey_eq_resolve key self).trans (indexed.resolve_sound key self)

/-- Unrelated keys may change, and receiver identities may differ. Reusing the
recipe requires equality of the actual ordered defaults and method payloads. -/
theorem IndexedPlan.prepareKey_frame {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (left right : IndexedPlan Key Value) (key : Key)
    (same : left.keyProjection key = right.keyProjection key) :
    left.prepareKey key = right.prepareKey key := by
  simp only [IndexedPlan.prepareKey, same]

/-- Projection visits C4 layers, not the catalog of all keys. This is an
enumeration bound on this function, not a hash-latency or native-cost proof. -/
theorem IndexedPlan.keyProjection_length {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key) :
    (indexed.keyProjection key).length = indexed.layers.length := by
  simp [IndexedPlan.keyProjection]

namespace OrderedContributions

/- The native prototype map permits multiple contributions at the same key.
The last-write-wins declaration model above cannot justify dropping those
rows: every computed contribution may request sup. This index retains the
whole chronological bucket, without binding it to a receiver. -/

def matching {Key Payload : Type} [DecidableEq Key]
    (rows : List (Key × Payload)) (key : Key) : List Payload :=
  rows.filterMap fun row => if row.1 = key then some row.2 else none

def push {Key Payload : Type} [BEq Key] [LawfulBEq Key] [Hashable Key]
    (table : Std.DHashMap Key (fun _ => List Payload)) (row : Key × Payload) :=
  table.insert row.1 (row.2 :: (table.get? row.1).getD [])

/-- One chronological admission pass. Each contribution uses a cons, never
append to a growing bucket. This is an algorithm, not a latency theorem for
the host's hash implementation. -/
def build {Key Payload : Type} [BEq Key] [LawfulBEq Key] [Hashable Key]
    (rows : List (Key × Payload)) : Std.DHashMap Key (fun _ => List Payload) :=
  rows.foldl push {}

private theorem fold_bucket {Key Payload : Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key] [DecidableEq Key]
    (rows : List (Key × Payload))
    (table : Std.DHashMap Key (fun _ => List Payload)) (key : Key) :
    ((rows.foldl push table).get? key).getD [] =
      (matching rows key).reverse ++ (table.get? key).getD [] := by
  induction rows generalizing table with
  | nil => simp [matching]
  | cons row rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rcases row with ⟨name, payload⟩
    by_cases same : name = key
    · subst name
      simp [push, matching, List.reverse_cons,
        List.append_assoc]
    · simp [push, Std.DHashMap.get?_insert, matching, same]

/-- Reversing only the selected bucket reproduces every contribution in
its original order, including duplicates. No receiver/value state is stored. -/
theorem bucket_exact {Key Payload : Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key] [DecidableEq Key]
    (rows : List (Key × Payload)) (key : Key) :
    (((build rows).get? key).getD []).reverse = matching rows key := by
  rw [build, fold_bucket]
  simp

/-- A concrete sibling insertion changes neither the ordered payloads nor
their multiplicity. An issuer must still authenticate that source edit. -/
theorem other_key_frame {Key Payload : Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key] [DecidableEq Key]
    (before after : List (Key × Payload)) (key changed : Key)
    (payload : Payload) (other : changed ≠ key) :
    (((build (before ++ (changed, payload) :: after)).get? key).getD []).reverse =
      (((build (before ++ after)).get? key).getD []).reverse := by
  simp [bucket_exact, matching, List.filterMap_append, other]

/-- Native prototype-map stores the first ordinal followed by later ordinals
in reverse insertion order. That spine is not already chronological. The
singleton physical representation is a scalar, normalized here to one item. -/
def chronologicalPositions : List Nat → List Nat
  | [] => []
  | first :: later => first :: later.reverse

def addPosition : List Nat → Nat → List Nat
  | [], position => [position]
  | first :: later, position => first :: position :: later

theorem positions_append_exact (positions : List Nat) (position : Nat) :
    chronologicalPositions (addPosition positions position) =
      chronologicalPositions positions ++ [position] := by
  cases positions <;> simp [chronologicalPositions, addPosition, List.reverse_cons]

theorem duplicate_position_control :
    chronologicalPositions [0, 3, 2, 1] = [0, 1, 2, 3] := rfl

def reference {Key Receiver Result : Type} [DecidableEq Key]
    (rows : List (Key × Prototype.SlotSpec Receiver Result)) (key : Key)
    (parent : Prototype.Method Receiver Result) : Prototype.Method Receiver Result :=
  rows.foldl (fun inherited row =>
    if row.1 = key then row.2.withParent inherited else inherited) parent

theorem matching_fold {Key Receiver Result : Type} [DecidableEq Key]
    (rows : List (Key × Prototype.SlotSpec Receiver Result)) (key : Key)
    (parent : Prototype.Method Receiver Result) :
    (matching rows key).foldl (fun inherited spec => spec.withParent inherited) parent =
      reference rows key parent := by
  induction rows generalizing parent with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.1 = key <;>
      simp [matching, reference, same, List.foldl_cons] at *
    · exact ih _
    · exact ih _

/-- The indexed bucket composes the exact same methods for arbitrary final
self and delayed sup. This does not certify native admission, source capture,
default-pass ordering, hooks, or the cost of building the index. -/
theorem indexed_fold_exact {Key Receiver Result : Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key] [DecidableEq Key]
    (rows : List (Key × Prototype.SlotSpec Receiver Result)) (key : Key)
    (parent : Prototype.Method Receiver Result) :
    ((((build rows).get? key).getD []).reverse).foldl
      (fun inherited spec => spec.withParent inherited) parent =
      reference rows key parent := by
  rw [bucket_exact, matching_fold]

private def repeated : List (Nat × Prototype.SlotSpec Unit Nat) :=
  [(0, .constant 1), (0, .modify (· + 2)), (1, .constant 99), (0, .modify (· * 3))]

/-- Collapsing a native bucket to either its first or last method loses sup.
The indexed resolver must preserve all three contributions: (1 + 2) * 3. -/
theorem duplicate_methods_are_not_last_write_wins :
    reference repeated 0 Prototype.Method.identity () (fun _ => 0) = 9 ∧
    (Prototype.SlotSpec.modify (· * 3)).withParent
      Prototype.Method.identity () (fun _ => 0) = 0 := by
  constructor <;> rfl

end OrderedContributions

private def preparedReceiverControl : Self Nat (fun _ => Nat) → Option Nat :=
  prepareProjectedKey (key := 0)
    [(some 10, none), (none, some (.self fun self => self 1)),
      (none, some (.computed fun _ inherited => (inherited ()).map (· + 2)))]

-- A shared method recipe must not share a computed receiver value.
#guard preparedReceiverControl (fun _ => some 7) == some 9
#guard preparedReceiverControl (fun _ => some 20) == some 22
#guard (prepareProjectedKey (Key := Nat) (Value := fun _ => Nat) (key := 0)
    [(some 10, none), (none, some (.computed fun _ inherited =>
      (inherited ()).map (· + 2)))]) (fun _ => none) == some 12
#guard (prepareProjectedKey (Key := Nat) (Value := fun _ => Bool) (key := 0)
    [(none, some (.constant (some false)))]) (fun _ => none) == some false
#guard (prepareProjectedKey (Key := Nat) (Value := fun _ => Bool) (key := 0)
    []) (fun _ => some false) == none

end LeanPoo.Object
