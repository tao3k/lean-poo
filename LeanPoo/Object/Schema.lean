import LeanPoo.C4.Linearize
import LeanPoo.Prototype.SlotSpec

/-!
The declaration and slot-resolution boundary follows François-René Rideau's
Gerbil-POO object.ss.
This Lean rewrite uses Apache-2.0.
-/

namespace LeanPoo.Object

universe u v w

/-- Each key fixes its value type. A missing slot is represented explicitly. -/
abbrev Self (Key : Type u) (Value : Key → Type v) :=
  (key : Key) → Option (Value key)

/-- One dependent keyed value. It carries the equality decision needed for
typed lookup, so read operations do not require a global key type class. -/
structure Entry (Key : Type u) (Payload : Key → Type w) where
  key : Key
  value : Payload key
  decideEq : (query : Key) → Decidable (query = key)

/-- The last direct declaration at a key wins, following ordered writes. -/
def Entry.lookup {Key : Type u} {Payload : Key → Type w}
    (entries : List (Entry Key Payload)) (key : Key) : Option (Payload key) :=
  entries.foldl (fun found (entry : Entry Key Payload) =>
    letI : Decidable (key = entry.key) := entry.decideEq key
    if same : key = entry.key then some (same.symm ▸ entry.value)
    else found) none

/-- Replacing an existing key keeps its declaration position. -/
def Entry.replace {Key : Type u} {Payload : Key → Type w}
    [DecidableEq Key] (entries : List (Entry Key Payload))
    (key : Key) (value : Payload key) : List (Entry Key Payload) :=
  let replacement : Entry Key Payload := ⟨key, value, fun _ => inferInstance⟩
  if entries.any (fun entry => decide (entry.key = key)) then
    entries.map (fun entry => if entry.key = key then replacement else entry)
  else entries ++ [replacement]

abbrev SlotPayload (Key : Type u) (Value : Key → Type v) (key : Key) :=
  Prototype.SlotSpec (Self Key Value) (Option (Value key))

/-- Direct slots and defaults retain the order in which keys were declared. -/
structure Declaration (Key : Type u) (Value : Key → Type v) where
  slots : List (Entry Key (SlotPayload Key Value))
  defaults : List (Entry Key Value)

def Declaration.empty : Declaration Key Value := ⟨[], []⟩

def Declaration.slot (declaration : Declaration Key Value) (key : Key) :
    Option (Prototype.SlotSpec (Self Key Value) (Option (Value key))) :=
  Entry.lookup declaration.slots key

def Declaration.default (declaration : Declaration Key Value) (key : Key) :
    Option (Value key) :=
  Entry.lookup declaration.defaults key

/-- Ordered direct keys come from the declaration itself. -/
def Declaration.directKeys (declaration : Declaration Key Value) : List Key :=
  declaration.slots.map Entry.key ++ declaration.defaults.map Entry.key

def Declaration.withSlot [DecidableEq Key]
    (declaration : Declaration Key Value) (key : Key)
    (spec : Prototype.SlotSpec (Self Key Value) (Option (Value key))) :
    Declaration Key Value :=
  { declaration with slots := Entry.replace declaration.slots key spec }

def Declaration.withDefault [DecidableEq Key]
    (declaration : Declaration Key Value) (key : Key) (value : Value key) :
    Declaration Key Value :=
  { declaration with defaults := Entry.replace declaration.defaults key value }

/-- Replace one direct slot with a constant value, as object.ss .cc does. -/
def Declaration.withValue [DecidableEq Key]
    (declaration : Declaration Key Value) (key : Key) (value : Value key) :
    Declaration Key Value :=
  declaration.withSlot key (.constant (some value))

/-- Translate object.ss object<-alist using dependent key/value pairs. -/
def Declaration.fromValues [DecidableEq Key]
    (entries : List (Sigma Value)) : Declaration Key Value :=
  entries.foldl (fun declaration entry =>
    declaration.withValue entry.1 entry.2) .empty

/-- Build direct values from a dependent map in caller-chosen key order.
This is the typed analogue of object<-hash's sorted traversal. -/
def Declaration.fromMap [DecidableEq Key] [BEq Key] [Hashable Key]
    (entries : Std.DHashMap Key Value) (lessEq : Key → Key → Bool) :
    Declaration Key Value :=
  Declaration.fromValues (entries.toList.mergeSort
    (fun left right => lessEq left.1 right.1))

/-- Translate object.ss object<-fun; values are requested only at lookup. -/
def Declaration.fromFunction [DecidableEq Key]
    (keys : List Key) (compute : (key : Key) → Value key) :
    Declaration Key Value :=
  keys.foldl (fun declaration key =>
    declaration.withSlot key (.thunk (fun _ => some (compute key)))) .empty

/-- C4 owns topology; declarations supply the methods for each node. -/
structure Schema (Key : Type u) (Value : Key → Type v) where
  graph : C4.Graph
  declaration : String → Option (Declaration Key Value)

inductive SchemaMergeError where
  | duplicateNode (name : String)
  deriving Repr, BEq

/-- Join independently built object families when their node identities do
not overlap. Existing names remain owned by the schema that declared them. -/
def Schema.mergeDisjoint (left right : Schema Key Value) :
    Except SchemaMergeError (Schema Key Value) :=
  match right.graph.nodes.find? (fun node =>
    (left.graph.findNode? node.name).isSome) with
  | some duplicate => .error (.duplicateNode duplicate.name)
  | none => .ok {
      graph := { nodes := left.graph.nodes ++ right.graph.nodes }
      declaration := fun name =>
        if (left.graph.findNode? name).isSome then left.declaration name
        else right.declaration name }

/-- Persistently revise one existing prototype declaration. -/
def Schema.reviseDeclaration (schema : Schema Key Value) (name : String)
    (update : Declaration Key Value → Declaration Key Value) :
    Except C4.Error (Schema Key Value) :=
  if (schema.graph.findNode? name).isNone then
    .error (.unknownNode name)
  else
    .ok { schema with declaration := fun query =>
      if query == name then some (update ((schema.declaration name).getD Declaration.empty))
      else schema.declaration query }

end LeanPoo.Object
