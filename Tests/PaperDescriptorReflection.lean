import LeanPoo.Prototype.DescriptorReflection
import LeanPoo.Prototype.NumberDescriptor
import LeanPoo.Prototype.PrototypeReflection
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperDescriptorReflection
private def run : IO Unit := do
  let integer := NumberDescriptor.int
  unless integer.zero == 0 && integer.one == 1 && integer.add 23 42 == 65 &&
      integer.subtract 8 4 == 4 && integer.descriptor.accepts (-23) do throw (IO.userError "Number source slots")
  let rational := NumberDescriptor.rational
  unless rational.add ((1 : Rat)/2) ((1 : Rat)/3) == (5 : Rat)/6 do throw (IO.userError "rational Number")
  let bounded : NumberDescriptor Int := { integer with descriptor := Descriptor.intRange 0 5 }
  unless (bounded.checkedAdd 2 3).toOption == some 5 && !(bounded.checkedAdd 5 1).isOk &&
      !(bounded.checkedAdd (-1) 2).isOk && !(bounded.checkedSubtract 1 2).isOk do
    throw (IO.userError "checked Number boundary")
  let element := Descriptor.intRange 0 100
  let description := DescriptorReflection.description element
  let self := DescriptorReflection.selfOf element
  unless self.accepts element && (DescriptorReflection.selfOf self).accepts self do
    throw (IO.userError "descriptor self-description")
  let record := DescriptorReflection.toRecord element
  let renamed ← IO.ofExcept (description.set record .name "Score")
  let rebuilt ← IO.ofExcept (DescriptorReflection.fromRecord renamed)
  unless rebuilt.name == "Score" && element.name != "Score" && rebuilt.accepts 42 && !rebuilt.accepts 101 do
    throw (IO.userError "typed field update or retained descriptor")
  unless !(description.set record .name "").isOk do throw (IO.userError "empty descriptor name admitted")
  let narrow : RecordDescription DescriptorReflection.Field (DescriptorReflection.Value Int) :=
    { description with keys := [.name] }
  unless !(narrow.set record .display toString).isOk do throw (IO.userError "undeclared reflection update admitted")
  for field in description.keys do
    let incomplete := { record with lookup := fun query => if query == field then none else record.lookup query }
    unless !(DescriptorReflection.fromRecord incomplete).isOk && !description.accepts incomplete do
      throw (IO.userError "missing reflected field admitted")
  let inspected ← IO.ofExcept (description.inspect renamed)
  unless (inspected.getObjValAs? String "name").toOption == some "Score" do
    throw (IO.userError "generated descriptor inspection")
  let fields ← IO.ofExcept ((← IO.ofExcept (description.schema.getObjVal? "fields")).getArr?)
  unless fields.size == 5 do throw (IO.userError "generated descriptor schema")
  let some codec := element.json | throw (IO.userError "missing integer codec")
  let codecRecord := DescriptorReflection.codecRecord codec
  let codecDescription := DescriptorReflection.codecDescription element
  unless codecDescription.accepts codecRecord && (DescriptorReflection.codecOf element).accepts codec do
    throw (IO.userError "codec self-description")
  let _ ← IO.ofExcept (codecDescription.inspect codecRecord)
  let good : DescriptorClass Int := fun _ inherited => { inherited.get with name := "Child" }
  let bad : DescriptorClass Int := fun _ inherited => { inherited.get with prototypeValue := some (-1) }
  unless (DescriptorReflection.classOf element).accepts good &&
      (DescriptorReflection.checkedClass element good (Thunk.pure element) (Thunk.pure element)).isOk &&
      !(DescriptorReflection.checkedClass element bad (Thunk.pure element) (Thunk.pure element)).isOk do
    throw (IO.userError "descriptor factory output admission")
  for value in List.range 101 do
    let descriptor ← IO.ofExcept (element.withPrototypeValue (Int.ofNat value))
    let rebuilt ← IO.ofExcept (DescriptorReflection.fromRecord (DescriptorReflection.toRecord descriptor))
    unless self.accepts descriptor && rebuilt.prototypeValue == descriptor.prototypeValue &&
        (← IO.ofExcept (rebuilt.decodeJson (← IO.ofExcept (descriptor.encodeJson (Int.ofNat value)))) ) == Int.ofNat value do
      throw (IO.userError "reflected descriptor scalar/codec oracle")
  IO.println "POOF-DESCRIPTORS-OK sourceNumber=true reflectedFields=5 codecFields=2 contexts=101 nestedSelf=true missingFields=5 generatedSchema=true"
#eval run
private unsafe def objects : IO Unit := do
  let element := (Descriptor.top "Nat" toString : Descriptor Nat).withJson
  let baseForces ← IO.mkRef (0 : Nat)
  let base : Thunk Nat := Thunk.mk fun _ => unsafeBaseIO do
    baseForces.modify (·+1)
    return 0
  let object := Object.ofPrototype (DelayedProto.constant 42) base
  let catalog := PrototypeReflection.description element
  let reflected := PrototypeReflection.toRecord object
  let rebuilt ← IO.ofExcept (PrototypeReflection.fromRecord reflected)
  let _ ← IO.ofExcept (catalog.inspect reflected)
  unless rebuilt.value == 42 && (← baseForces.get) == 0 do
    throw (IO.userError "object reflection forced inherited base or changed value")
  let metadata := MetaPrototype.make (DelayedProto.constant 43) ["Parent"] ["Child","Parent"]
  let metaCatalog := PrototypeReflection.metaDescription element
  let _ ← IO.ofExcept (metaCatalog.inspect metadata.value)
  let objectCatalog := PrototypeReflection.metaObjectDescription element
  let _ ← IO.ofExcept (objectCatalog.inspect (PrototypeReflection.toRecord metadata))
  let mutated ← IO.ofExcept (metaCatalog.set metadata.value .supers ["Other"])
  unless mutated.lookup .supers == some ["Other"] && metadata.value.lookup .supers == some ["Parent"] do
    throw (IO.userError "meta description typed update or retained metadata")
  let decoded ← IO.ofExcept (((metaCatalog.field .supers).decodeJson (Lean.toJson (["A","B"] : List String))))
  unless decoded == ["A","B"] do throw (IO.userError "generated meta list field decoder")
  IO.println "POOF-PROTOTYPE-REFLECTION-OK objectFields=3 metaFields=3 metaObject=true inheritedBaseUnforced=true typedUpdate=true"
#eval objects
#print axioms PrototypeReflection.fromRecord_toRecord
#print axioms DescriptorReflection.fromRecord_toRecord
end LeanPoo.Tests.PaperDescriptorReflection
