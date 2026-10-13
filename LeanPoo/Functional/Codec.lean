import LeanPoo.Functional.Validation
import LeanPoo.Prototype.Class

/-! Executable descriptor operations for typed values, constraints and nested
representations. The law is decode-after-encode for valid values. -/
namespace LeanPoo.Functional
universe u v w x y

structure Codec (Value : Type u) (Wire : Type v) (Error : Type w) where
  encode : Value → Wire
  decode : Wire → Except Error Value
  decode_encode : ∀ value, decode (encode value) = .ok value

namespace Codec
variable {Value : Type u} {Wire : Type v} {Error : Type w}

def identity (Value : Type u) (Error : Type w) : Codec Value Value Error :=
  ⟨id, Except.ok, fun _ => rfl⟩

/-- Convert the public value representation using explicit inverse functions. -/
def transport (codec : Codec Value Wire Error) {Other : Type x}
    (forward : Value → Other) (backward : Other → Value)
    (inverse : ∀ other, forward (backward other) = other) : Codec Other Wire Error where
  encode value := codec.encode (backward value)
  decode wire := (codec.decode wire).map forward
  decode_encode value := by simp [codec.decode_encode, inverse, Except.map]

/-- Change the wire representation while keeping the admitted value carrier. -/
def represent (codec : Codec Value Wire Error) {Other : Type x}
    (pack : Wire → Other) (unpack : Other → Wire)
    (inverse : ∀ wire, unpack (pack wire) = wire) : Codec Value Other Error where
  encode value := pack (codec.encode value)
  decode wire := codec.decode (unpack wire)
  decode_encode value := by simp [inverse, codec.decode_encode]

@[simp] theorem represent_decode (codec : Codec Value Wire Error) {Other : Type x}
    (pack : Wire → Other) (unpack : Other → Wire)
    (inverse : ∀ wire, unpack (pack wire) = wire) (wire : Wire) :
    (codec.represent pack unpack inverse).decode (pack wire) = codec.decode wire := by
  simp [represent, inverse]

/-- Add a runtime predicate check and return its proof with every success. -/
def refine (codec : Codec Value Wire Error) (predicate : Value → Prop)
    [DecidablePred predicate] (invalid : Error) : Codec {value : Value // predicate value} Wire Error where
  encode value := codec.encode value.val
  decode wire := (codec.decode wire).bind fun value =>
    if valid : predicate value then .ok ⟨value, valid⟩ else .error invalid
  decode_encode value := by simp [Except.bind, codec.decode_encode, value.property]

/-- Decode the left component before the right, preserving the exact error. -/
def product (left : Codec Value Wire Error) {Other : Type x} {Representation : Type y}
    (right : Codec Other Representation Error) : Codec (Value × Other) (Wire × Representation) Error where
  encode value := (left.encode value.1, right.encode value.2)
  decode wire := (left.decode wire.1).bind fun first =>
    (right.decode wire.2).map (first, ·)
  decode_encode value := by simp [Except.bind, Except.map, left.decode_encode, right.decode_encode]

/-- Nested batches use the same first-error traversal as factory validation. -/
def list (codec : Codec Value Wire Error) : Codec (List Value) (List Wire) Error where
  encode values := values.map codec.encode
  decode := Validation.traverse codec.decode
  decode_encode values := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp [Except.bind, Except.map, Validation.traverse, codec.decode_encode, ih]

theorem refine_decode_error (codec : Codec Value Wire Error) (predicate : Value → Prop)
    [DecidablePred predicate] (invalid : Error) (wire : Wire)
    (error : Error) (failed : codec.decode wire = .error error) :
    (codec.refine predicate invalid).decode wire = .error error := by
  simp [refine, failed, Except.bind]

theorem refine_rejected (codec : Codec Value Wire Error) (predicate : Value → Prop)
    [DecidablePred predicate] (invalid : Error) (wire : Wire) (value : Value)
    (decoded : codec.decode wire = .ok value) (rejected : ¬ predicate value) :
    (codec.refine predicate invalid).decode wire = .error invalid := by
  simp [refine, decoded, rejected, Except.bind]

/-- Admit an existing descriptor JSON codec only with its explicit roundtrip law. -/
def ofJson {Value : Type} (codec : Prototype.JsonCodec Value)
    (roundtrip : ∀ value, codec.decode (codec.encode value) = .ok value) : Codec Value Lean.Json String :=
  ⟨codec.encode, codec.decode, roundtrip⟩

/-- Erase the proof to attach these operations to an existing Descriptor. -/
def toJson {Value : Type} (codec : Codec Value Lean.Json String) : Prototype.JsonCodec Value :=
  ⟨codec.encode, codec.decode⟩

theorem toJson_roundtrip {Value : Type} (codec : Codec Value Lean.Json String) (value : Value) :
    codec.toJson.decode (codec.toJson.encode value) = .ok value := codec.decode_encode value

end Codec
end LeanPoo.Functional
