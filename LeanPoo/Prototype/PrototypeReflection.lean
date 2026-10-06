import LeanPoo.Prototype.DescriptorReflection
import LeanPoo.Prototype.MetaPrototype

namespace LeanPoo.Prototype.PrototypeReflection

/-- Runtime refinement of a delayed value; inspecting it explicitly forces it. -/
def delayedOf (element : Descriptor α) : Descriptor (Thunk α) :=
  { name := s!"Thunk {element.name}"
    accepts := fun value => element.accepts value.get
    display := fun value => element.display value.get }

/-- Describe a typed open-recursive prototype without forcing final self.
Input/output refinement is checked on applications, not universally on closures. -/
def prototypeOf (element : Descriptor α) : Descriptor (DelayedProto α α α) :=
  Descriptor.top s!"DelayedProto {element.name}" (fun _ => "open self/inherited computation")

inductive Field where | prototype | base | result deriving BEq, DecidableEq
abbrev Value (α : Type) : Field → Type
  | .prototype => DelayedProto α α α
  | .base | .result => Thunk α

def toRecord (object : Object α α) : Record Field (Value α) :=
  { lookup := fun field => match field with
    | .prototype => some object.prototype | .base => some object.base | .result => some object.result }

private def require (value : Option α) (name : String) : Except String α :=
  match value with | some item => .ok item | none => .error s!"missing object field: {name}"

def fromRecord (record : Record Field (Value α)) : Except String (Object α α) := do
  return { prototype := ← require (record.lookup .prototype) "prototype"
           base := ← require (record.lookup .base) "base"
           result := ← require (record.lookup .result) "result" }

theorem fromRecord_toRecord (object : Object α α) :
    fromRecord (toRecord object) = .ok object := by cases object; rfl

def description (element : Descriptor α) : RecordDescription Field (Value α) :=
  { name := s!"Object {element.name}"
    keys := [.prototype,.base,.result]
    label := fun field => match field with
      | .prototype => "prototype" | .base => "base" | .result => "result"
    field := fun field => match field with
      | .prototype => prototypeOf element
      | .base => Descriptor.top s!"Inherited Thunk {element.name}" (fun _ => "unforced inherited value")
      | .result => delayedOf element }

/-- Metadata slots are described with the same generic dependent-record API. -/
def metaDescription (element : Descriptor α) :
    RecordDescription MetaPrototype.Slot (MetaPrototype.Value α) :=
  { name := s!"MetaPrototype {element.name}"
    keys := [.function,.supers,.precedence]
    label := fun field => match field with
      | .function => "function" | .supers => "supers" | .precedence => "precedence"
    field := fun field => match field with
      | .function => prototypeOf element
      | .supers | .precedence => ((Descriptor.top "String" id).withJson).listOf }

/-- Describe object metadata itself by applying the ordinary Object catalog to
its described record carrier. No distinct reflection engine is needed. -/
def metaObjectDescription (element : Descriptor α) :
    RecordDescription Field (Value (MetaPrototype.MetaRecord α)) :=
  description (metaDescription element).toDescriptor

end LeanPoo.Prototype.PrototypeReflection
