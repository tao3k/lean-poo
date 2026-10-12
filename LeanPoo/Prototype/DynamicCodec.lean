import Lean
import LeanPoo.Prototype.DynamicDescriptorSemantics

/-! Strict structural JSON for dynamic values and descriptor-owned admission.
Functions and descriptors serialize only registered identities; closures do
not cross the wire. Admission checks every nested identity in the current
registry before checking the descriptor's refinement. -/
namespace LeanPoo.Prototype.Dynamic

inductive WireError where
  | malformed (message : String)
  | budgetExhausted
  | admission (error : Error)
  | rejected (descriptor : String)
  deriving Repr, BEq

def Value.encodeJson : Value → Lean.Json
  | .unit => .arr #[.str "unit"]
  | .boolean value => .arr #[.str "boolean", .bool value]
  | .integer value => .arr #[.str "integer", .str (toString value)]
  | .text value => .arr #[.str "text", .str value]
  | .list values => .arr #[.str "list", .arr (values.map Value.encodeJson).toArray]
  | .dictionary entries => .arr #[.str "dictionary", .arr (entries.map fun entry =>
      Lean.Json.arr #[entry.1.encodeJson, entry.2.encodeJson]).toArray]
  | .object slots => .arr #[.str "object", .arr (slots.map fun entry =>
      Lean.Json.arr #[.str entry.1, entry.2.encodeJson]).toArray]
  | .function identity => .arr #[.str "function", .str identity]
  | .descriptor identity => .arr #[.str "descriptor", .str identity]
termination_by value => sizeOf value
decreasing_by
  all_goals first | decreasing_trivial | skip
  all_goals rename_i member
  all_goals have smaller := List.sizeOf_lt_of_mem member
  all_goals cases entry
  all_goals simp_all
  all_goals omega

/-- Array tags and exact arities preserve order and duplicate dictionary or
object entries without relying on a JSON object's key-collapsing parser. -/
def Value.decodeJson : Nat → Lean.Json → Except WireError Value
  | 0, _ => .error .budgetExhausted
  | fuel + 1, raw => do
    let .arr fields := raw | throw (.malformed "expected a tagged value array")
    match fields.toList with
    | [.str "unit"] => return .unit
    | [.str "boolean", .bool value] => return .boolean value
    | [.str "integer", .str source] =>
      let some value := source.toInt? | throw (.malformed "invalid exact integer")
      if toString value != source then throw (.malformed "noncanonical exact integer")
      return .integer value
    | [.str "text", .str value] => return .text value
    | [.str "function", .str identity] => return .function identity
    | [.str "descriptor", .str identity] => return .descriptor identity
    | [.str "list", .arr values] => return .list (← values.toList.mapM (Value.decodeJson fuel))
    | [.str "dictionary", .arr entries] =>
      return .dictionary (← entries.toList.mapM fun raw => do
        let .arr fields := raw | throw (.malformed "expected a dictionary entry")
        let [key, value] := fields.toList | throw (.malformed "expected two dictionary entry values")
        return (← Value.decodeJson fuel key, ← Value.decodeJson fuel value))
    | [.str "object", .arr entries] =>
      return .object (← entries.toList.mapM fun raw => do
        let .arr fields := raw | throw (.malformed "expected an object entry")
        let [.str key, value] := fields.toList | throw (.malformed "expected an object key and value")
        return (key, ← Value.decodeJson fuel value))
    | _ => throw (.malformed "unknown value tag, invalid payload or extra fields")

def Value.checkReferences (registry : Registry) : Nat → Value → Except Error Unit
  | 0, _ => .error .budgetExhausted
  | fuel + 1, value =>
    match value with
    | .function identity =>
      if (registry.function? identity).isSome then .ok () else .error (.unknownFunction identity)
    | .descriptor identity =>
      if (registry.descriptor? identity).isSome then .ok () else .error (.unknownDescriptor identity)
    | .list values => do
      let _ ← values.mapM (Value.checkReferences registry fuel)
      return ()
    | .dictionary entries => do
      let _ ← entries.mapM fun entry => do
        Value.checkReferences registry fuel entry.1
        Value.checkReferences registry fuel entry.2
      return ()
    | .object entries => do
      let _ ← entries.mapM fun entry => Value.checkReferences registry fuel entry.2
      return ()
    | _ => .ok ()

structure Admitted (registry : Registry) (contract : Contract) where
  value : Value
  valid : Accepted registry contract value

def Descriptor.validate (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (value : Value) : Except WireError (Admitted registry descriptor.contract) := do
  (value.checkReferences registry fuel).mapError WireError.admission
  match checked : descriptor.accepts registry fuel value with
  | .error error => throw (.admission error)
  | .ok false => throw (.rejected descriptor.name)
  | .ok true => return ⟨value, accepts_sound registry fuel descriptor.contract value checked⟩

theorem Descriptor.validate_value (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (value : Value) (admitted : Admitted registry descriptor.contract)
    (success : descriptor.validate registry fuel value = .ok admitted) : admitted.value = value := by
  unfold Descriptor.validate at success
  cases references : value.checkReferences registry fuel with
  | error error => simp [references, Except.mapError, bind, Except.bind] at success
  | ok unitValue =>
    simp only [references, Except.mapError, bind, Except.bind] at success
    split at success
    · simp at success
    · simp at success
    · simp only [pure, Except.pure, Except.ok.injEq] at success
      cases success
      rfl

def Descriptor.encodeJson (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (value : Value) : Except WireError Lean.Json := do
  let accepted ← descriptor.validate registry fuel value
  return accepted.value.encodeJson

def Descriptor.decodeJson (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (raw : Lean.Json) : Except WireError (Admitted registry descriptor.contract) := do
  descriptor.validate registry fuel (← Value.decodeJson fuel raw)

def Descriptor.encodeText (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (value : Value) : Except WireError String :=
  (descriptor.encodeJson registry fuel value).map Lean.Json.compress

def Descriptor.decodeText (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (text : String) : Except WireError (Admitted registry descriptor.contract) := do
  descriptor.decodeJson registry fuel (← (Lean.Json.parse text).mapError WireError.malformed)

def Descriptor.encodeBytes (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (value : Value) : Except WireError ByteArray :=
  (descriptor.encodeText registry fuel value).map String.toUTF8

def Descriptor.decodeBytes (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (bytes : ByteArray) : Except WireError (Admitted registry descriptor.contract) := do
  let some text := String.fromUTF8? bytes | throw (.malformed "invalid UTF-8")
  descriptor.decodeText registry fuel text

end LeanPoo.Prototype.Dynamic
