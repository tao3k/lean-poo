import LeanPoo.Prototype.RecordDescription

/-! Typed self-description of descriptors, codecs and descriptor-class
functions. Generated validation/schema/inspection reuse the field catalog.
Callable types are checked by Lean; no universal function behavior test is
claimed and no callable closure is decoded from JSON. -/
namespace LeanPoo.Prototype.DescriptorReflection

inductive Field where | name | accepts | display | prototypeValue | json deriving DecidableEq, BEq
abbrev Value (α : Type) : Field → Type
  | .name => String
  | .accepts => α → Bool
  | .display => α → String
  | .prototypeValue => Option α
  | .json => Option (JsonCodec α)

inductive CodecField where | encode | decode deriving DecidableEq, BEq
abbrev CodecValue (α : Type) : CodecField → Type
  | .encode => α → Lean.Json
  | .decode => Lean.Json → Except String α

def codecRecord (codec : JsonCodec α) : Record CodecField (CodecValue α) :=
  { lookup := fun key => match key with
    | .encode => some codec.encode | .decode => some codec.decode }

def codecDescription (element : Descriptor α) : RecordDescription CodecField (CodecValue α) :=
  { name := s!"JsonCodec {element.name}"
    keys := [.encode,.decode]
    label := fun key => match key with | .encode => "encode" | .decode => "decode"
    field := fun key => match key with
      | .encode => Descriptor.functionOf element (Descriptor.top "Json" (fun _ => "JSON"))
      | .decode => Descriptor.functionOf (Descriptor.top "Json" (fun _ => "JSON"))
        (Descriptor.top s!"Except String {element.name}" (fun _ => "checked decode")) }

def codecOf (element : Descriptor α) : Descriptor (JsonCodec α) :=
  { name := s!"JsonCodec {element.name}"
    accepts := fun codec => (codecDescription element).accepts (codecRecord codec)
    display := fun _ => s!"JsonCodec {element.name}" }

def toRecord (descriptor : Descriptor α) : Record Field (Value α) :=
  { lookup := fun key => match key with
    | .name => some descriptor.name | .accepts => some descriptor.accepts
    | .display => some descriptor.display | .prototypeValue => some descriptor.prototypeValue
    | .json => some descriptor.json }

private def require (value : Option α) (name : String) : Except String α :=
  match value with | some item => .ok item | none => .error s!"missing descriptor field: {name}"

def fromRecord (record : Record Field (Value α)) : Except String (Descriptor α) := do
  return { name := ← require (record.lookup .name) "name"
           accepts := ← require (record.lookup .accepts) "accepts"
           display := ← require (record.lookup .display) "display"
           prototypeValue := ← require (record.lookup .prototypeValue) "prototypeValue"
           json := ← require (record.lookup .json) "json" }

/-- Structural field reconstruction is exact, including function/codec values. -/
theorem fromRecord_toRecord (descriptor : Descriptor α) :
    fromRecord (toRecord descriptor) = .ok descriptor := by cases descriptor; rfl

def description (element : Descriptor α) : RecordDescription Field (Value α) :=
  { name := s!"Descriptor {element.name}"
    keys := [.name,.accepts,.display,.prototypeValue,.json]
    label := fun field => match field with
      | .name => "name" | .accepts => "accepts" | .display => "display"
      | .prototypeValue => "prototypeValue" | .json => "json"
    field := fun field => match field with
      | .name => (Descriptor.top "Name" id).withJson |>.refine "NonemptyName" (!·.isEmpty)
      | .accepts => Descriptor.functionOf element (Descriptor.top "Bool" toString)
      | .display => Descriptor.functionOf element (Descriptor.top "String" id)
      | .prototypeValue => element.optionOf
      | .json => (codecOf element).optionOf }

/-- A descriptor of descriptors. The optional default must also satisfy the
described refinement; the returned descriptor can itself be described again. -/
def selfOf (element : Descriptor α) : Descriptor (Descriptor α) :=
  { name := s!"Descriptor {element.name}"
    accepts := fun descriptor => (description element).accepts (toRecord descriptor) &&
      descriptor.prototypeValue.all descriptor.accepts
    display := fun descriptor => s!"descriptor {descriptor.name}" }

def classOf (element : Descriptor α) : Descriptor (DescriptorClass α) :=
  Descriptor.top s!"DescriptorClass {element.name}" (fun _ => "delayed descriptor prototype")

/-- Checked application for descriptor factories; static class typing alone
cannot prove the produced refinement or a callable's universal behavior. -/
def checkedClass (element : Descriptor α) (prototype : DescriptorClass α)
    (self inherited : Thunk (Descriptor α)) : Except String (Descriptor α) :=
  (selfOf element).validate (prototype self inherited)

end LeanPoo.Prototype.DescriptorReflection
