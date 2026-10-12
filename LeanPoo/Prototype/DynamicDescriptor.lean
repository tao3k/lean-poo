import LeanPoo.Prototype.Compose

/-! A recursive dynamic value universe and first-class runtime descriptors.
Functions and descriptors have registry identities, so negative function
occurrences need not be embedded in an inductive Lean value. Function contracts
validate both call boundaries. They do not decide universal function properties. -/
namespace LeanPoo.Prototype.Dynamic

inductive Value where
  | unit
  | boolean (value : Bool)
  | integer (value : Int)
  | text (value : String)
  | list (values : List Value)
  | dictionary (entries : List (Value × Value))
  | object (slots : List (String × Value))
  | function (identity : String)
  | descriptor (identity : String)
  deriving Repr, BEq

inductive Contract where
  | top
  | bottom
  | unit
  | boolean
  | integer
  | integerRange (lower upper : Int)
  | text
  | listOf (element : Contract)
  | dictionaryOf (key value : Contract)
  | objectOf (slots : List (String × Contract))
  | functionOf (input output : Contract)
  | descriptor
  | named (identity : String)
  | union (left right : Contract)
  | intersection (left right : Contract)
  deriving Repr, BEq

/-- Metadata is an open dynamic object, allowing descriptor-specific slots. -/
structure Descriptor where
  name : String
  contract : Contract
  metadata : List (String × Value) := []
  deriving Repr

inductive Error where
  | budgetExhausted
  | unknownDescriptor (identity : String)
  | unknownFunction (identity : String)
  | expectedFunction
  | expectedDescriptor
  | expectedFunctionContract
  | argumentRejected (descriptor : String)
  | resultRejected (descriptor : String)
  | functionError (message : String)
  deriving Repr, BEq, DecidableEq

structure Registry where
  descriptors : List (String × Descriptor) := []
  functions : List (String × (Value → Except Error Value)) := []

def Registry.descriptor? (registry : Registry) (identity : String) : Option Descriptor :=
  (registry.descriptors.find? (fun entry => entry.1 == identity)).map Prod.snd

def Registry.function? (registry : Registry) (identity : String) :
    Option (Value → Except Error Value) :=
  (registry.functions.find? (fun entry => entry.1 == identity)).map Prod.snd

def Value.slot? (value : Value) (key : String) : Option Value :=
  match value with
  | .object slots => (slots.find? (fun entry => entry.1 == key)).map Prod.snd
  | _ => none

/-- Membership can recurse through arbitrary values and named descriptor
graphs. Exhausting the supplied depth is a typed error, never a rejection. -/
def accepts (registry : Registry) : Nat → Contract → Value → Except Error Bool
  | 0, _, _ => .error .budgetExhausted
  | fuel + 1, contract, value =>
    match contract, value with
    | .top, _ => .ok true
    | .bottom, _ => .ok false
    | .unit, .unit | .boolean, .boolean _ | .integer, .integer _ | .text, .text _ => .ok true
    | .integerRange lower upper, .integer number => .ok (lower ≤ number && number ≤ upper)
    | .listOf element, .list values => do
      let checks ← values.mapM (accepts registry fuel element)
      return checks.all id
    | .dictionaryOf key value, .dictionary entries => do
      let checks ← entries.mapM fun entry => do
        let keyOk ← accepts registry fuel key entry.1
        let valueOk ← accepts registry fuel value entry.2
        return keyOk && valueOk
      return checks.all id
    | .objectOf slots, .object fields => do
      let checks ← slots.mapM fun (key, contract) => do
        let some field := (fields.find? (fun entry => entry.1 == key)).map Prod.snd |
          return false
        accepts registry fuel contract field
      return checks.all id
    | .functionOf _ _, .function identity => .ok (registry.function? identity).isSome
    | .descriptor, .descriptor identity => .ok (registry.descriptor? identity).isSome
    | .named identity, value => do
      let some descriptor := registry.descriptor? identity | throw (.unknownDescriptor identity)
      accepts registry fuel descriptor.contract value
    | .union left right, value => do
      let leftOk ← accepts registry fuel left value
      if leftOk then return true
      accepts registry fuel right value
    | .intersection left right, value => do
      let leftOk ← accepts registry fuel left value
      if !leftOk then return false
      accepts registry fuel right value
    | _, _ => .ok false

def Descriptor.accepts (descriptor : Descriptor) (registry : Registry)
    (fuel : Nat) (value : Value) : Except Error Bool :=
  Dynamic.accepts registry fuel descriptor.contract value

/-- The actual callable value and both dynamic refinements are checked. -/
def Descriptor.call (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (function : Value) (argument : Value) : Except Error Value := do
  let .functionOf input output := descriptor.contract | throw .expectedFunctionContract
  let .function identity := function | throw .expectedFunction
  let some callable := registry.function? identity | throw (.unknownFunction identity)
  unless ← Dynamic.accepts registry fuel input argument do throw (.argumentRejected descriptor.name)
  let result ← callable argument
  unless ← Dynamic.accepts registry fuel output result do throw (.resultRejected descriptor.name)
  return result

def Descriptor.functionOf (input output : Descriptor) : Descriptor :=
  ⟨s!"{input.name} → {output.name}", .functionOf input.contract output.contract, []⟩

/-- Every contract exposes its constructor and arguments as ordinary dynamic
data. Named references retain their identities, including recursive types. -/
def Contract.describe : Contract → Value
  | .top => .object [("constructor", .text "top")]
  | .bottom => .object [("constructor", .text "bottom")]
  | .unit => .object [("constructor", .text "unit")]
  | .boolean => .object [("constructor", .text "boolean")]
  | .integer => .object [("constructor", .text "integer")]
  | .integerRange lower upper => .object [("constructor", .text "integerRange"),
      ("lower", .integer lower), ("upper", .integer upper)]
  | .text => .object [("constructor", .text "text")]
  | .listOf element => .object [("constructor", .text "listOf"), ("element", element.describe)]
  | .dictionaryOf key value => .object [("constructor", .text "dictionaryOf"),
      ("key", key.describe), ("value", value.describe)]
  | .objectOf slots => .object [("constructor", .text "objectOf"),
      ("slots", .object (slots.map fun entry => (entry.1, entry.2.describe)))]
  | .functionOf input output => .object [("constructor", .text "functionOf"),
      ("input", input.describe), ("output", output.describe)]
  | .descriptor => .object [("constructor", .text "descriptor")]
  | .named identity => .object [("constructor", .text "named"), ("identity", .text identity)]
  | .union left right => .object [("constructor", .text "union"),
      ("left", left.describe), ("right", right.describe)]
  | .intersection left right => .object [("constructor", .text "intersection"),
      ("left", left.describe), ("right", right.describe)]
termination_by contract => sizeOf contract
decreasing_by
  all_goals first | decreasing_trivial | skip
  rename_i member
  have smaller := List.sizeOf_lt_of_mem member
  cases entry
  simp_all
  omega

def Descriptor.describe (descriptor : Descriptor) : Value :=
  .object (("name", .text descriptor.name) :: ("contract", descriptor.contract.describe) :: descriptor.metadata)

/-- First-class descriptor values resolve through the supplied current registry. -/
def Registry.inspect (registry : Registry) (value : Value) : Except Error Value :=
  match value with
  | .descriptor identity =>
    match registry.descriptor? identity with
    | some descriptor => .ok descriptor.describe
    | none => .error (.unknownDescriptor identity)
  | _ => .error .expectedDescriptor

/-- Runtime descriptors themselves inhabit the same dynamic value universe. -/
def descriptorType : Descriptor := ⟨"Descriptor", .descriptor, []⟩

abbrev Class := Proto Descriptor Descriptor Descriptor

def Class.withContract (contract : Contract) : Class :=
  fun _ inherited => { inherited with contract }

def Class.withSlot (key : String) (compute : Descriptor → Value) : Class :=
  fun self inherited => { inherited with metadata := (key, compute self) :: inherited.metadata }

end LeanPoo.Prototype.Dynamic
