import LeanPoo.Prototype.MVP

namespace LeanPoo.Examples.RecordPrototype

open LeanPoo.Prototype

inductive Key where
  | x | y | sum
  deriving DecidableEq

abbrev Value : Key → Type := fun _ => Nat

def layers : Proto (Record Key Value) (Record Key Value)
    (Record Key Value) :=
  compose (Record.compute .sum fun self =>
      (self.lookup .x).getD 0 + (self.lookup .y).getD 0)
    (compose (Record.modify .x (· * 2))
      (compose (Record.slot .x 3) (Record.slot .y 2)))

unsafe def result : Record Key Value :=
  Record.instantiate layers Record.empty

/-- Inheritance order is observable when one layer reads the inherited slot. -/
unsafe def modifiedThenSet : Record Key Value :=
  Record.instantiate
    (compose (Record.modify .x (· * 2)) (Record.slot .x 3)) Record.empty

unsafe def setThenModified : Record Key Value :=
  Record.instantiate
    (compose (Record.slot .x 3) (Record.modify .x (· * 2))) Record.empty

#eval (result.lookup .x, result.lookup .y, result.lookup .sum)
#eval (modifiedThenSet.lookup .x, setThenModified.lookup .x)

end LeanPoo.Examples.RecordPrototype
