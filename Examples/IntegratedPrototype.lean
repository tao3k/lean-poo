import LeanPoo.Object.Prototype
import LeanPoo.Object.Mutable
import LeanPoo.Object.Generic
import LeanPoo.Object.Lens
import LeanPoo.Object.Class
import LeanPoo.Prototype.Class
import LeanPoo.Prototype.Types

namespace LeanPoo.Examples.IntegratedPrototype

def emptySchema : Object.Schema String (fun _ => Nat) :=
  { graph := { nodes := [] }, declaration := fun _ => none }

def base : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withValue "retries" 2 |>.withValue "scale" 2

def left : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "retries"
    (.computed fun _ inherited => some ((inherited ()).getD 0 + 1))

def right : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "retries"
    (.computed fun _ inherited => some ((inherited ()).getD 0 + 10))

/-- This slot reads the final object, including any later override. -/
def diamond : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withSlot "total"
    (.self fun self => some (2 * (self "retries").getD 0))

def override : Object.Declaration String (fun _ => Nat) :=
  Object.Declaration.empty |>.withValue "retries" 5 |>.withValue "scale" 3

/-- The same local override as a normal delayed prototype, for extending
the first-class projection without going through a new C4 declaration. -/
def overridePrototype : Prototype.DelayedProto
    (Object.Self String (fun _ => Nat))
    (Object.Self String (fun _ => Nat))
    (Object.Self String (fun _ => Nat)) :=
  fun _ inherited => fun key =>
    if key == "retries" then some 5 else inherited.get key

/-- One shared ancestor appears only once in the C4 precedence. -/
def compiled : Except C4.Error (Object.Plan String (fun _ => Nat)) := do
  let basePlan ← LeanPoo.mix emptySchema "Base" [] base
  let leftPlan ← LeanPoo.extend basePlan.schema "Left" "Base" left
  let rightPlan ← LeanPoo.extend leftPlan.schema "Right" "Base" right
  LeanPoo.mix rightPlan.schema "Diamond" ["Left", "Right"] diamond

/-- C4 metadata also handles an inherited suffix tail and multiple local
parent orders, beyond the ordinary diamond used for object values. -/
def c4MetadataRun : Except C4.Error (List String × List String) := do
  let suffixGraph : C4.Graph := { nodes :=
    [{ name := "Object", suffix := true },
     { name := "Named", parentOrders := [["Object"]], suffix := true },
     { name := "Printable", parentOrders := [["Named"]] },
     { name := "Loggable", parentOrders := [["Named"]] },
     { name := "Service", parentOrders := [["Printable", "Loggable"]] }] }
  let parentOrderGraph : C4.Graph := { nodes :=
    [{ name := "Object" },
     { name := "A", parentOrders := [["Object"]] },
     { name := "B", parentOrders := [["Object"]] },
     { name := "C", parentOrders := [["Object"]] },
     { name := "Example", parentOrders := [["A", "B"], ["C"]] }] }
  return (← C4.linearize suffixGraph "Service",
    ← C4.linearize parentOrderGraph "Example")

def c4RejectionRun : Bool × Bool :=
  let cycle : C4.Graph := { nodes :=
    [{ name := "A", parentOrders := [["B"]] },
     { name := "B", parentOrders := [["A"]] }] }
  let conflict : C4.Graph := { nodes :=
    [{ name := "O" },
     { name := "A", parentOrders := [["O"]] },
     { name := "B", parentOrders := [["O"]] },
     { name := "X", parentOrders := [["A", "B"]] },
     { name := "Y", parentOrders := [["B", "A"]] },
     { name := "Z", parentOrders := [["X", "Y"]] }] }
  (match C4.linearize cycle "A" with
    | .error (.cycle "A") => true
    | _ => false,
   match C4.linearize conflict "Z" with
    | .error .inconsistentOrder => true
    | _ => false)

/-- Both the C4 and first-class extensions rebind final self to the override.
The first-class extension remains explicitly unsafe because it ties a general
open-recursive fixed point. -/
unsafe def pureRun : Except C4.Error
    (List String × Option Nat × Option Nat × Option Nat × Option Nat × Option Nat) := do
  let plan ← compiled
  let object := plan.memoize
  let firstClass := object.toFirstClassObject
  let extended ← object.extend "Override" override
  let extendedFirstClass := firstClass.extend overridePrototype
  return (plan.precedence, object.read "retries", object.read "total",
    firstClass.value "total", extended.read "total",
    extendedFirstClass.value "total")

def totalBase : Prototype.Descriptor Nat :=
  ({ name := "Natural total"
     accepts := fun _ => true
     display := toString } : Prototype.Descriptor Nat).withJson

def largeTotal : Prototype.DescriptorClass Nat :=
  fun _ inherited => inherited.get.refine "Large total" (· >= 20)

/-- A class is itself a prototype for the runtime descriptor of the same
numeric values produced by the object model. -/
unsafe def classRun : Except C4.Error (Bool × Bool) := do
  let plan ← compiled
  let object := plan.memoize
  let extended ← object.extend "Override" override
  let descriptor := (Prototype.DescriptorClass.instantiate largeTotal totalBase).value
  return (descriptor.accepts ((object.read "total").getD 0),
    descriptor.accepts ((extended.read "total").getD 0))

/-- Native option, product, and sum types preserve descriptor recognition
without rebuilding a dynamic Scheme type language. -/
unsafe def typeRun : Bool × Bool × Bool × Bool × Bool :=
  let descriptor := (Prototype.DescriptorClass.instantiate largeTotal totalBase).value
  ((descriptor.optionOf).accepts (some 26),
    (descriptor.pairOf descriptor).accepts (26, 10),
    (descriptor.sumOf descriptor).accepts (Sum.inr 26),
    (descriptor.exactly 26).accepts 26,
    (descriptor.oneOf [26, 30]).accepts 10)

/-- Runtime refinement checks also apply after decoding. Built-in Lean JSON
instances supply primitive encoding; descriptor combinators carry it through
option, product, and sum types. -/
unsafe def jsonRun : Except String
    (Nat × Bool × Bool × Bool × Bool × Bool × Bool × Bool) := do
  let descriptor := (Prototype.DescriptorClass.instantiate largeTotal totalBase).value
  let encoded ← descriptor.encodeJson 26
  let decoded ← descriptor.decodeJson encoded
  let rejectsSmall := match descriptor.decodeJson (Lean.toJson (10 : Nat)) with
    | .error _ => true
    | .ok _ => false
  let optional := descriptor.optionOf
  let optionRoundTrip ← optional.decodeJson (← optional.encodeJson (some 26))
  let paired := descriptor.pairOf descriptor
  let pairRoundTrip ← paired.decodeJson (← paired.encodeJson (26, 26))
  let array := descriptor.arrayOf
  let arrayRoundTrip ← array.decodeJson (← array.encodeJson #[26, 30])
  let mapped := descriptor.stringMapOf
  let source : Std.HashMap String Nat := ({} : Std.HashMap String Nat).insert "answer" 26
  let mapRoundTrip ← mapped.decodeJson (← mapped.encodeJson source)
  let byteRoundTrip ← descriptor.decodeBytes (← descriptor.encodeBytes 26)
  let textRoundTrip ← descriptor.decodeText (← descriptor.encodeText 26)
  return (decoded, rejectsSmall, optionRoundTrip == some 26,
    pairRoundTrip == (26, 26), arrayRoundTrip == #[26, 30],
    mapRoundTrip.get? "answer" == some 26, byteRoundTrip == 26,
    textRoundTrip == 26)

def boundedNumberRun : Except String (Nat × Bool) := do
  let descriptor := Prototype.Descriptor.fin 5
  let encoded ← descriptor.encodeJson (⟨3, by decide⟩ : Fin 5)
  let decoded ← descriptor.decodeJson encoded
  let rejectsOutOfRange := match descriptor.decodeJson (Lean.toJson (8 : Nat)) with
    | .error _ => true
    | .ok _ => false
  return (decoded.val, rejectsOutOfRange)

/-- Arbitrary bytes, fixed-length refinement, and union/intersection of
runtime refinements reuse the same typed JSON boundary. -/
def compositeTypeRun : Except String
    (Bool × Bool × Bool × Bool × Bool × Bool × Bool) := do
  let fixedBytes := Prototype.Descriptor.bytesN 3
  let bytes := ByteArray.mk #[0, 127, 255]
  let roundTrip ← fixedBytes.decodeJson (← fixedBytes.encodeJson bytes)
  let badLength := match fixedBytes.decodeJson
      (Lean.Json.arr #[Lean.toJson (1 : Nat)]) with
    | .error _ => true
    | .ok _ => false
  let numbers := totalBase.exactly 26 |>.union (totalBase.exactly 30)
  let unionRoundTrip ← numbers.decodeJson (← numbers.encodeJson 30)
  let intersection := totalBase.refine "at least twenty" (· >= 20)
    |>.intersect (totalBase.refine "even" (fun value => value % 2 == 0))
  let positive := totalBase.refine "positive" (· > 0)
  let large := totalBase.refine "large" (· >= 20)
  let checked ← positive.checkedCall large (· + 20) 3
  let badOutput := match positive.checkedCall large (fun _ => 1) 3 with
    | .error _ => true
    | .ok _ => false
  let jsonValue :=
    ((Prototype.Descriptor.top "Json" Lean.Json.compress) :
      Prototype.Descriptor Lean.Json).withJson
  let optional := jsonValue.optionOf
  let someNull ← optional.decodeJson (← optional.encodeJson (some Lean.Json.null))
  return (roundTrip == bytes, badLength, unionRoundTrip == 30,
    intersection.accepts 26 && !intersection.accepts 21,
    checked == 23, badOutput, someNull == some Lean.Json.null)

/-- The heterogeneous tuple's element types are fixed by a type-level
list; its runtime descriptors refine and serialize those same positions. -/
def heterogeneousTupleRun : Except String Bool :=
  let boolean :=
    ((Prototype.Descriptor.top "Bool" toString) :
      Prototype.Descriptor Bool).withJson
  let descriptors : Prototype.Descriptors [Nat, Bool] :=
    .cons totalBase (.cons boolean .nil)
  let tuple : Prototype.HList [Nat, Bool] := .cons 26 (.cons true .nil)
  let descriptor := descriptors.toDescriptor
  match descriptor.encodeJson tuple with
  | .error error => .error error
  | .ok encoded =>
    match descriptor.decodeJson encoded with
    | .error error => .error error
    | .ok (.cons number (.cons flag .nil)) =>
      .ok (number == 26 && flag && descriptor.accepts tuple)

def numericTypeRun : Except String (Bool × Bool × Bool × Bool × Bool) := do
  let range := Prototype.Descriptor.intRange (-5) 5
  let valid ← range.decodeJson (← range.encodeJson 3)
  let rejectsRange := match range.decodeJson (Lean.toJson (8 : Int)) with
    | .error _ => true
    | .ok _ => false
  let word := Prototype.Descriptor.bitVec 8
  let decodedWord ← word.decodeJson (← word.encodeJson (BitVec.ofNat 8 255))
  let signed := Prototype.Descriptor.signedBitVec 8
  let signedWord ← signed.decodeJson (← signed.encodeJson (BitVec.ofInt 8 (-12)))
  let rejectsSigned := match signed.decodeJson (Lean.toJson (128 : Int)) with
    | .error _ => true
    | .ok _ => false
  let rational := Prototype.Descriptor.rational
  let value := Rat.normalize 3 4
  let decodedRatio ← rational.decodeJson (← rational.encodeJson value)
  return (valid == 3 && rejectsRange,
    decodedWord.toNat == 255,
    signedWord.toInt == -12 && rejectsSigned,
    decodedRatio.num == value.num && decodedRatio.den == value.den,
    (Prototype.TypedValue.make totalBase 26).isSome &&
      !(Prototype.TypedValue.make (totalBase.exactly 26) 10).isSome)

def descriptorPrototypeRun : Except String (Bool × Bool) := do
  let descriptor ← totalBase.withPrototypeValue 12
  let rule := Object.SlotRule.fromDescriptor (Value := fun _ => Nat)
    "retries" descriptor
  let rejectsBad := match (totalBase.exactly 26).withPrototypeValue 12 with
    | .error _ => true
    | .ok _ => false
  return (rule.default == some 12, rejectsBad)

def mapTypeRun : Except String (Bool × Bool) := do
  let descriptor := totalBase.mapOf Prototype.TextCodec.nat
  let source : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert 3 26
  let decoded ← descriptor.decodeJson (← descriptor.encodeJson source)
  let collision := Lean.Json.mkObj
    [("1", Lean.toJson (26 : Nat)), ("01", Lean.toJson (30 : Nat))]
  let rejectsCollision := match descriptor.decodeJson collision with
    | .error _ => true
    | .ok _ => false
  return (decoded.get? 3 == some 26, rejectsCollision)

/-- Generic method selection reads the same C4 slot instance. The explicit
fallback is used when no method slot exists. -/
def genericRun : Except C4.Error (Nat × Nat × Nat × Nat) := do
  let plan ← compiled
  let object := plan.memoize
  let extended ← object.extend "Override" override
  let scale : Object.Generic (Object.Memoized String (fun _ => Nat)) Nat Nat Nat :=
    Object.Generic.fromSlot "scale" (fun factor _ input => factor * input)
      (fun _ input => input)
  let absent : Object.Generic (Object.Memoized String (fun _ => Nat)) Nat Nat Nat :=
    Object.Generic.fromSlot "missing" (fun factor _ input => factor * input)
      (fun _ input => input)
  return (scale.call object 3, scale.call extended 3,
    absent.call object 3, object.refWith "missing" (fun _ => 99))

/-- The class descriptor validates an object through its existing lazy
slots. Its typed defaults can seed a new declaration without another object
representation. -/
def objectClass : Object.ClassSpec String (fun _ => Nat) :=
  { name := "Large retry object"
    rules :=
      [({ key := "retries", default := some 12 } : Object.SlotRule String (fun _ => Nat)).withJson,
       (Object.SlotRule.constant "scale" 2).withJson,
       { (Object.SlotRule.fromDescriptor (Value := fun _ => Nat) "total"
           (totalBase.refine "Large total" (· >= 20))) with
         compute := some (.self fun self => some (2 * (self "retries").getD 0)) },
       { key := "note", optional := true }]
    sealed := true }

def objectClassRun : Except C4.Error (Bool × Bool × Option Nat × Option Nat) := do
  let plan ← compiled
  let object := plan.memoize
  let extended ← object.extend "Override" override
  let constructed ← objectClass.instantiate
  let descriptor := objectClass.toDescriptor
  return (descriptor.accepts object, descriptor.accepts extended,
    constructed.read "scale", constructed.read "total")

/-- The class descriptor can itself be instantiated from a delayed
prototype. Child rules override parent rules at matching keys. -/
unsafe def classLayerRun : Except C4.Error (Bool × Bool × Option Nat) := do
  let plan ← compiled
  let original := plan.memoize
  let changed ← original.extend "HighOverride"
    (Object.Declaration.empty |>.withValue "retries" 15 |>.withValue "scale" 3)
  let layer := Object.ClassSpec.layer "Scaled retry object"
    [Object.SlotRule.constant "scale" 3]
    true
  let derivedClass := (Prototype.Object.ofPrototype layer (Thunk.pure objectClass)).value
  let constructed ← derivedClass.instantiate
  return (derivedClass.acceptsObject changed,
    derivedClass.acceptsObject original, constructed.read "total")

/-- Construction and validation agree on the last declaration of a key. -/
def repeatedClassRuleRun : Except C4.Error (Bool × Option Nat × Bool) := do
  let revised := { objectClass with
    rules := objectClass.rules ++ [Object.SlotRule.constant "scale" 3] }
  let constructed ← revised.instantiate
  return (revised.acceptsObject constructed, constructed.read "scale",
    revised.effectiveRules.length == objectClass.effectiveRules.length)

/-- A type-selected generic takes its operation from a runtime class
descriptor, while Lean fixes the receiver, argument, and result types. -/
def typeGenericRun : Except C4.Error (Nat × Nat) := do
  let plan ← compiled
  let original := plan.memoize
  let changed ← original.extend "Override" override
  let typeGeneric : Object.Generic (Object.Memoized String (fun _ => Nat))
      Nat Nat Nat := Object.Generic.fromType
    (fun object => if objectClass.acceptsObject object then
        objectClass.toDescriptor else
        { objectClass.toDescriptor with name := "Other retry object" })
    (fun descriptor => if descriptor.name == objectClass.name then some 4 else some 5)
    (fun factor _ argument => factor * argument)
    (fun _ argument => argument)
  return (typeGeneric.call original 3, typeGeneric.call changed 3)

/-- A slot lens updates the persistent root declaration, forcing a new
instance while the original object keeps its memoized values. -/
def slotLensRun : Except C4.Error
    (Except (Object.SlotLensError String) (Nat × Nat × Nat)) := do
  let plan ← compiled
  let original := plan.memoize
  return do
    let lens := Object.Lens.slot (Value := fun _ => Nat) "retries"
    let prior ← lens.get original
    let changed ← lens.modify (· + 2) original
    return (prior, (changed.read "total").getD 0,
      (original.read "total").getD 0)

def objectClassJsonRun : Except C4.Error (Except String (Option Nat × Bool × Bool)) := do
  let plan ← compiled
  let object := plan.memoize
  return do
    let encoded ← objectClass.encodeJson id object
    let decoded ← (objectClass.decodeObjectJson id encoded).mapError reprStr
    let unknownRejected := match objectClass.decodeJson id
        (encoded.setObjVal! "unexpected" (Lean.toJson (1 : Nat))) with
      | .error _ => true
      | .ok _ => false
    return (decoded.read "total", objectClass.acceptsObject decoded,
      unknownRejected)

/-- A mutable identity installs the new pure object while an old snapshot
continues to observe its own immutable, memoized instance. -/
def mutableRun : IO (Except C4.Error (Option Nat × Option Nat × Option Nat)) := do
  match compiled with
  | .error error => return .error error
  | .ok plan =>
    let mutableObject ← Object.Mutable.new plan.memoize
    let before ← mutableObject.snapshot
    match ← mutableObject.extend "Override" override with
    | .error error => return .error error
    | .ok () =>
      let middle ← mutableObject.snapshot
      match ← mutableObject.putValue "retries" 7 with
      | .error error => return .error error
      | .ok () =>
        let after ← mutableObject.read "total"
        return .ok (before.read "total", middle.read "total", after)

#eval pureRun
#eval c4MetadataRun
#eval c4RejectionRun
#eval classRun
#eval typeRun
#eval jsonRun
#eval boundedNumberRun
#eval compositeTypeRun
#eval heterogeneousTupleRun
#eval numericTypeRun
#eval descriptorPrototypeRun
#eval mapTypeRun
#eval genericRun
#eval objectClassRun
#eval classLayerRun
#eval repeatedClassRuleRun
#eval typeGenericRun
#eval slotLensRun
#eval objectClassJsonRun
#eval mutableRun

end LeanPoo.Examples.IntegratedPrototype
