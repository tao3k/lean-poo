import LeanPoo.Prototype.Class

namespace LeanPoo.Tests.DescriptorClass

open LeanPoo.Prototype

def natBase : Descriptor Nat :=
  { name := "Natural"
    accepts := fun _ => true
    display := toString }

def evenClass : Prototype.DescriptorClass Nat :=
  fun _ inherited =>
    { name := "Even natural"
      accepts := fun value => inherited.get.accepts value && value % 2 == 0
      display := inherited.get.display }

unsafe def evenNumbers : Prototype.Object (Descriptor Nat) (Descriptor Nat) :=
  Prototype.DescriptorClass.instantiate evenClass natBase

unsafe def positiveEvenNumbers : Prototype.Object (Descriptor Nat) (Descriptor Nat) :=
  evenNumbers.extend (fun _ inherited =>
    { inherited.get with
      name := "Positive even natural"
      accepts := fun value => inherited.get.accepts value && value > 0 })

#eval (evenNumbers.value.accepts 2, evenNumbers.value.accepts 3,
  positiveEvenNumbers.value.accepts 0,
  (positiveEvenNumbers.value.listOf).accepts [2, 4])

end LeanPoo.Tests.DescriptorClass
