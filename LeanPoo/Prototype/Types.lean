import LeanPoo.Prototype.Class

/-!
Lean-native heterogeneous tuples: their element types are tracked by a
type-level list. Runtime descriptors refine those static types and supply
JSON codecs only when every component has one.
-/

namespace LeanPoo.Prototype

inductive HList : List Type → Type 1 where
  | nil : HList []
  | cons {α : Type} {rest : List Type} : α → HList rest → HList (α :: rest)

inductive Descriptors : List Type → Type 1 where
  | nil : Descriptors []
  | cons {α : Type} {rest : List Type} :
      Descriptor α → Descriptors rest → Descriptors (α :: rest)

inductive Codecs : List Type → Type 1 where
  | nil : Codecs []
  | cons {α : Type} {rest : List Type} :
      JsonCodec α → Codecs rest → Codecs (α :: rest)

def Descriptors.accepts : {types : List Type} →
    Descriptors types → HList types → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons descriptor rest, .cons value values =>
      descriptor.accepts value && rest.accepts values

def Descriptors.codecs : {types : List Type} →
    Descriptors types → Option (Codecs types)
  | [], .nil => some .nil
  | _ :: _, .cons descriptor rest =>
      match descriptor.json, rest.codecs with
      | some codec, some codecs => some (.cons codec codecs)
      | _, _ => none

def Codecs.encode : {types : List Type} →
    Codecs types → HList types → List Lean.Json
  | [], .nil, .nil => []
  | _ :: _, .cons codec rest, .cons value values =>
      codec.encode value :: rest.encode values

def Codecs.decode : {types : List Type} →
    Codecs types → List Lean.Json → Except String (HList types)
  | [], .nil, [] => return .nil
  | [], .nil, _ => throw "too many tuple elements"
  | _ :: _, .cons codec rest, raw :: raws =>
      match codec.decode raw with
      | .error error => .error error
      | .ok value =>
        match rest.decode raws with
        | .error error => .error error
        | .ok values => .ok (.cons value values)
  | _ :: _, .cons _ _, [] => throw "too few tuple elements"

def Descriptors.toDescriptor {types : List Type}
    (descriptors : Descriptors types) : Descriptor (HList types) :=
  { name := "Tuple"
    accepts := descriptors.accepts
    display := fun _ => s!"tuple of {types.length} elements"
    json := descriptors.codecs.map fun codecs =>
      { encode := fun values => Lean.Json.arr (codecs.encode values).toArray
        decode := fun raw =>
          match raw.getArr? with
          | .error error => .error error
          | .ok values => codecs.decode values.toList } }

/-- A value paired with its runtime descriptor. Lean remembers the carrier
type and evidence that the descriptor recognizes this particular value. -/
structure TypedValue where
  carrier : Type
  descriptor : Descriptor carrier
  value : carrier
  accepted : descriptor.accepts value = true

def TypedValue.make (descriptor : Descriptor α) (value : α) : Option TypedValue :=
  if accepted : descriptor.accepts value = true then
    some ⟨α, descriptor, value, accepted⟩
  else none

/-- Runtime range checking complements Lean's statically typed integers. -/
def Descriptor.intRange (lower upper : Int) : Descriptor Int :=
  ((Descriptor.top "Int" toString) : Descriptor Int).withJson
    |>.refine s!"Int {lower}..{upper}"
      (fun value => lower <= value && value <= upper)

/-- A fixed-width integer uses Lean's `BitVec` as its static carrier. -/
def Descriptor.bitVec (width : Nat) : Descriptor (BitVec width) :=
  { name := s!"BitVec {width}"
    accepts := fun _ => true
    display := fun value => toString value.toNat
    json := some {
      encode := fun value => Lean.toJson value.toNat
      decode := fun raw => do
        let value ← raw.getNat?
        if value < 2 ^ width then return BitVec.ofNat width value
        else throw s!"number outside BitVec {width}" } }

/-- The same fixed-width Lean carrier interpreted as a signed integer. -/
def Descriptor.signedBitVec (width : Nat) : Descriptor (BitVec width) :=
  { name := s!"SignedBitVec {width}"
    accepts := fun _ => true
    display := fun value => toString value.toInt
    json := some {
      encode := fun value => Lean.toJson value.toInt
      decode := fun raw => do
        let value ← raw.getInt?
        if width == 0 then
          if value == 0 then return BitVec.ofInt width value
          else throw "number outside SignedBitVec 0"
        else
          let bound := (2 : Int) ^ (width - 1)
          if -bound <= value && value < bound then
            return BitVec.ofInt width value
          else throw s!"number outside SignedBitVec {width}" } }

/-- Rat is the Lean-native normalized rational carrier. The decoder
requires a nonzero denominator before constructing a value. -/
def Descriptor.rational : Descriptor Rat :=
  { name := "Rational"
    accepts := fun _ => true
    display := fun value => s!"{value.num}/{value.den}"
    json := some {
      encode := fun value => Lean.Json.arr
        #[Lean.toJson value.num, Lean.toJson value.den]
      decode := fun raw => do
        let entries ← raw.getArr?
        match entries.toList with
        | [numerator, denominator] =>
          let num ← numerator.getInt?
          let den ← denominator.getNat?
          if positive : den ≠ 0 then
            return Rat.normalize num den positive
          else throw "zero rational denominator"
        | _ => throw "expected a numerator and denominator" } }

end LeanPoo.Prototype
