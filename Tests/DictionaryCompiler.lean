import LeanPoo.Deriving.DictionaryCompiler

namespace LeanPoo.Tests.DictionaryCompiler
open Prototype
universe u v

class Arithmetic (α : Type u) where
  zero : α
  add : α → α → α
  zero_add : ∀ value, add zero value = value
derive_dictionary Arithmetic

class NamedArithmetic (α : Type u) extends Arithmetic α where
  label : String
  named_zero : toArithmetic.add toArithmetic.zero toArithmetic.zero = toArithmetic.zero
derive_dictionary NamedArithmetic

structure CarrierDictionary where
  Carrier : Type u
  operations : Arithmetic Carrier
  value : Carrier
  law : operations.add operations.zero value = value
derive_dictionary CarrierDictionary

structure SortDictionary where
  Carrier : Sort u
  value : Carrier
derive_dictionary SortDictionary

class PolyFunction (α : Sort u) (β : Sort v) where
  run : α → β
derive_dictionary PolyFunction

class Indexed (n : Nat) where
  value : Fin n
  bound : value.val < n
derive_dictionary Indexed

structure Empty where
derive_dictionary Empty

class UsesInstance (α : Type u) [Inhabited α] where
  value : α
derive_dictionary UsesInstance

-- The same compiler also handles the library's actual type descriptor.
derive_dictionary LeanPoo.Prototype.Descriptor as DescriptorFields

example (dictionary : Arithmetic α) : Arithmetic.fromFields (Arithmetic.toFields dictionary) = dictionary :=
  Arithmetic.from_toFields dictionary
example (fields : Arithmetic.Fields (α := α)) : Arithmetic.toFields (Arithmetic.fromFields fields) = fields :=
  Arithmetic.to_fromFields fields
example (dictionary : CarrierDictionary.{u}) :
    CarrierDictionary.fromFields (CarrierDictionary.toFields dictionary) = dictionary :=
  CarrierDictionary.from_toFields dictionary
example (dictionary : SortDictionary.{u}) :
    SortDictionary.fromFields (SortDictionary.toFields dictionary) = dictionary :=
  SortDictionary.from_toFields dictionary
example (dictionary : PolyFunction α β) : PolyFunction.fromFields (PolyFunction.toFields dictionary) = dictionary :=
  PolyFunction.from_toFields dictionary
example (dictionary : Indexed n) : Indexed.fromFields (Indexed.toFields dictionary) = dictionary :=
  Indexed.from_toFields dictionary
example [Inhabited α] (dictionary : UsesInstance α) :
    UsesInstance.fromFields (UsesInstance.toFields dictionary) = dictionary := UsesInstance.from_toFields dictionary

-- A field representation cannot erase or fabricate the dictionary's law.
example : True := by
  fail_if_success
    have _bad : Arithmetic.Fields (α := Nat) :=
      ⟨⟨0, (fun x y => x+y+1), (by intro x; rfl), PUnit.unit⟩⟩
  trivial

/-- error: derive_dictionary expects a Type-valued structure or class: Nat -/
#guard_msgs in
derive_dictionary Nat

/-- error: derive_dictionary declaration already exists: LeanPoo.Tests.DictionaryCompiler.Arithmetic.Fields -/
#guard_msgs in
derive_dictionary Arithmetic

class OnlyLaw : Prop where
  law : True
/-- error: derive_dictionary cannot make a runtime descriptor from a Prop-valued class: LeanPoo.Tests.DictionaryCompiler.OnlyLaw -/
#guard_msgs in
derive_dictionary OnlyLaw
-- Refusal leaves no partially generated runtime schema.
example : True := by
  fail_if_success have _partial := OnlyLaw.Fields
  trivial

private instance natural : Arithmetic Nat := ⟨0, Nat.add, Nat.zero_add⟩
private abbrev named : NamedArithmetic Nat := { label := "natural", named_zero := rfl }
private abbrev carrier : CarrierDictionary := ⟨Nat, natural, 7, rfl⟩

#eval do
  IO.println "DICTIONARY-COMPILER-START"
  let dictionary := Arithmetic.fromFields (Arithmetic.toFields natural)
  let mut cases := 0
  for x in List.range 32 do
    for y in List.range 32 do
      letI : Arithmetic Nat := dictionary
      unless Arithmetic.add x y == x+y && Arithmetic.zero (α := Nat) == 0 do
        throw (IO.userError "generated dictionary changed typeclass dispatch")
      cases := cases+1
  let recovered := NamedArithmetic.fromFields (NamedArithmetic.toFields named)
  unless recovered.label == "natural" && recovered.add 4 9 == 13 do
    throw (IO.userError "inherited subdictionary changed")
  let restored := CarrierDictionary.fromFields (CarrierDictionary.toFields carrier)
  unless restored.operations.add restored.value restored.value == 14 do
    throw (IO.userError "dependent carrier/operations/value were separated")
  let proofCarrier : SortDictionary := ⟨True, True.intro⟩
  let _proofRestored := SortDictionary.fromFields (SortDictionary.toFields proofCarrier)
  let poly : PolyFunction Nat Bool := ⟨fun n => n % 2 == 0⟩
  let restored := PolyFunction.fromFields (PolyFunction.toFields poly)
  for n in List.range 33 do
    unless restored.run n == (n % 2 == 0) do throw (IO.userError "polymorphic function changed")
  let indexed : Indexed 8 := ⟨⟨7, by decide⟩, by decide⟩
  unless (Indexed.fromFields (Indexed.toFields indexed)).value.val == 7 do
    throw (IO.userError "index/proof changed")
  let _empty := Empty.fromFields (Empty.toFields ⟨⟩)
  let withInstance : UsesInstance Nat := ⟨3⟩
  unless (UsesInstance.fromFields (UsesInstance.toFields withInstance)).value == 3 do
    throw (IO.userError "instance parameter changed")
  let descriptor : Descriptor Nat := (Descriptor.top "Natural" toString).withJson
  let restored := DescriptorFields.fromFields (DescriptorFields.toFields descriptor)
  unless restored.name == descriptor.name && restored.display 17 == "17" && restored.accepts 17 do
    throw (IO.userError "actual descriptor representation changed")
  unless (Arithmetic.fieldNames == ["zero", "add", "zero_add"]) && Arithmetic.fieldCount == 3 &&
      CarrierDictionary.fieldCount == 4 && NamedArithmetic.fieldCount == 3 && Empty.fieldCount == 0 do
    throw (IO.userError s!"constructor field catalog changed: {Arithmetic.fieldNames}, {Arithmetic.fieldCount}, {CarrierDictionary.fieldCount}, {NamedArithmetic.fieldCount}, {Empty.fieldCount}")
  unless cases == 1024 do throw (IO.userError "dictionary dispatch coverage changed")
  IO.println s!"DICTIONARY-COMPILER-OK dispatch={cases} polymorphic=33 shapes=9 refusals=3"

#print axioms Arithmetic.from_toFields
#print axioms Arithmetic.to_fromFields
#print axioms CarrierDictionary.from_toFields
#print axioms CarrierDictionary.to_fromFields
#print axioms DescriptorFields.from_toFields
end LeanPoo.Tests.DictionaryCompiler
