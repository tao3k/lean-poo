import LeanPoo.Prototype.Object
import LeanPoo.Prototype.C3

/-! Typed metadata-prototype slots use the same delayed record/object constructors
as ordinary instances. String identifiers replace recursive untyped object
identity; a registry supplies the referenced super objects. -/
namespace LeanPoo.Prototype
namespace MetaPrototype

private def require (value : Option α) (message : String) : Except String α :=
  match value with
  | some item => .ok item
  | none => .error message

inductive Slot where | function | supers | precedence deriving DecidableEq
abbrev Layer (α : Type) := DelayedProto α α α
abbrev Value (α : Type) : Slot → Type
  | .function => Layer α
  | .supers | .precedence => List String
abbrev MetaRecord (α : Type) := Record Slot (Value α)
abbrev Meta (α : Type) := Object (MetaRecord α) (MetaRecord α)

/-- Metadata is an extensible first-class object, not a closed schema struct. -/
unsafe def make (function : Layer α) (supers precedence : List String) : Meta α :=
  Object.ofPrototype
    (DelayedProto.compose (Object.recordSlotGen .function (fun _ _ => some function))
      (DelayedProto.compose (Object.recordSlotGen .supers (fun _ _ => some supers))
        (Object.recordSlotGen .precedence (fun _ _ => some precedence))))
    (Thunk.pure Record.empty)

structure Instance (α : Type) where
  value : Thunk α
  metadata : Option (Meta α)
  /-- Special base case: use constant instance slots over the inherited instance. -/
  baseFunction : Layer α

/-- The special base case for records merges constant slots child over parent. -/
def fromRecord (record : Record Key Values) : Instance (Record Key Values) :=
  { value := Thunk.pure record
    metadata := none
    baseFunction := fun _ inherited =>
      { lookup := fun key => (record.lookup key).orElse (fun _ => inherited.get.lookup key) } }

def function (object : Instance α) : Except String (Layer α) :=
  match object.metadata with
  | none => .ok object.baseFunction
  | some metadata => require (metadata.value.lookup .function) "missing metadata function"

def supers (object : Instance α) : Except String (List String) :=
  match object.metadata with
  | none => .ok []
  | some metadata => require (metadata.value.lookup .supers) "missing metadata supers"

def precedence (object : Instance α) : Except String (List String) :=
  match object.metadata with
  | none => .ok []
  | some metadata => require (metadata.value.lookup .precedence) "missing metadata precedence"

abbrev Registry (α : Type) := List (String × Instance α)
private def find (registry : Registry α) (name : String) : Except String (Instance α) :=
  require ((registry.find? (fun entry => entry.1 == name)).map Prod.snd) s!"unknown super: {name}"

/-- Build a fresh C3 cache from final metadata and the parents' retained caches.
The cache is exposed as a normal metadata slot; caller overrides remain observable. -/
unsafe def instantiate (name : String) (metadata : Meta α) (registry : Registry α)
    (base : α) : Except String (Instance α) := do
  if registry.any (fun entry => entry.1 == name) then throw "duplicate object name"
  if (LeanPoo.C4.unique (registry.map Prod.fst)).length != registry.length then
    throw "duplicate registry name"
  let parents ← require (metadata.value.lookup .supers) "missing metadata supers"
  if (LeanPoo.C4.unique parents).length != parents.length then throw "duplicate direct super"
  let orders ← parents.mapM (fun parent => do precedence (← find registry parent))
  if orders.any (·.contains name) then throw "cyclic retained precedence"
  let merged ← (LeanPoo.C4.Precedence.mergeCertified (orders ++ [parents])).mapError (fun _ => "inconsistent C3 precedence")
  let order := name :: merged.output
  let own ← require (metadata.value.lookup .function) "missing metadata function"
  let inherited ← merged.output.mapM (fun parent => do function (← find registry parent))
  let combined := (own :: inherited).foldr DelayedProto.compose (fun _ parent => parent.get)
  let cached := metadata.extend (Object.recordSlotGen .precedence (fun _ _ => some order))
  return { value := DelayedProto.instantiate combined (Thunk.pure base)
           metadata := some cached
           baseFunction := fun _ parent => parent.get }

end MetaPrototype
end LeanPoo.Prototype
