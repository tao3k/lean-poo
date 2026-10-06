import LeanPoo.Prototype.Types

namespace LeanPoo.Prototype

/-- The source Number descriptor's recognizer/presentation and arithmetic
slots over a chosen Lean carrier. Subclasses may override individual methods. -/
structure NumberDescriptor (α : Type) where
  descriptor : Descriptor α
  add : α → α → α
  subtract : α → α → α
  zero : α
  one : α

def NumberDescriptor.ofTypeclasses [Add α] [Sub α] [Zero α] [OfNat α 1]
    (descriptor : Descriptor α) : NumberDescriptor α :=
  ⟨descriptor, (· + ·), (· - ·), 0, 1⟩

def NumberDescriptor.int : NumberDescriptor Int :=
  ofTypeclasses ((Descriptor.top "Int" toString : Descriptor Int).withJson)

def NumberDescriptor.rational : NumberDescriptor Rat :=
  ofTypeclasses Descriptor.rational

/-- Arithmetic respects both argument and result refinements. -/
def NumberDescriptor.checkedAdd (number : NumberDescriptor α) (left right : α) : Except String α := do
  let _ ← number.descriptor.validate left
  let _ ← number.descriptor.validate right
  number.descriptor.validate (number.add left right)

def NumberDescriptor.checkedSubtract (number : NumberDescriptor α) (left right : α) : Except String α := do
  let _ ← number.descriptor.validate left
  let _ ← number.descriptor.validate right
  number.descriptor.validate (number.subtract left right)

end LeanPoo.Prototype
