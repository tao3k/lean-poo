import LeanPoo.Prototype.RecordRepresentations

namespace LeanPoo.Examples.DictionaryRecords
open Prototype

-- The structural dictionary is a total solution of the original prototype
-- equations; only record instantiation below ties a general delayed self.
def scores : Except String (Tree Int String) :=
  (Dictionary.avl (Acc := Unit) OrderOps.integer).fromList
    [(3,"three"),(1,"one"),(2,"two"),(2,"replacement")]

def dictionaryReads : Except String (List (Option String)) := do
  let tree ← scores
  [1,2,3,4].mapM fun key => (Dictionary.avl (Acc := Unit) OrderOps.integer).ref tree key

#guard dictionaryReads.toOption == some [some "one",some "replacement",some "three",none]

unsafe def run : IO Unit := do
  IO.println s!"ordered dictionary reads: {repr dictionaryReads}"
  let base : DictionaryRecord Int Int := DictionaryRecord.fromOrder OrderOps.integer
  let slots := DelayedProto.compose
    (DictionaryRecord.compute 2 fun self => do return (← self.get 1) + 2)
    (DelayedProto.compose (DictionaryRecord.modify 1 (· * 2)) (DictionaryRecord.slot 1 3))
  let original := DictionaryRecord.instantiate slots base
  let derived := DictionaryRecord.instantiate
    (DelayedProto.compose (DictionaryRecord.slot 1 10) slots) base
  IO.println s!"original inherited/self values: {repr (original.get 1)}, {repr (original.get 2)}"
  IO.println s!"derived final-self value: {repr (derived.get 2)}"
  IO.println s!"retained original: {repr (original.get 2)}; missing: {repr (derived.get 9)}"

#eval run
end LeanPoo.Examples.DictionaryRecords
