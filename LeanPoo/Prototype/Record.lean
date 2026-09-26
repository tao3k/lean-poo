import LeanPoo.Prototype.Compose

/-!
The paper's first record-prototype construction, with Lean keys indexing
their value types. Each slot constructor below is a specialization of
`slotGen`; composition and fixed-point evaluation remain those of `Proto`.
-/

namespace LeanPoo.Prototype

/-- A record is a typed key-to-value function kept as runtime data. -/
structure Record (Key : Type) (Value : Key → Type) where
  lookup : (key : Key) → Option (Value key)
  runtimeAnchor : Nat := 0

def Record.empty : Record Key Value :=
  { lookup := fun _ => none }

/-- The general slot prototype: final self and inherited slot computation
are distinct inputs, and an override may leave inheritance unevaluated. -/
def Record.slotGen {Key : Type} {Value : Key → Type} [DecidableEq Key]
    (key : Key)
    (compute : Record Key Value → (Unit → Option (Value key)) →
      Option (Value key)) :
    Proto (Record Key Value) (Record Key Value) (Record Key Value) :=
  fun self inherited =>
    { lookup := fun query =>
        if same : query = key then
          same.symm ▸ compute self (fun _ => inherited.lookup key)
        else inherited.lookup query }

def Record.slot {Key : Type} {Value : Key → Type} [DecidableEq Key]
    (key : Key) (value : Value key) :
    Proto (Record Key Value) (Record Key Value) (Record Key Value) :=
  slotGen key (fun _ _ => some value)

def Record.modify {Key : Type} {Value : Key → Type} [DecidableEq Key]
    (key : Key) (change : Value key → Value key) :
    Proto (Record Key Value) (Record Key Value) (Record Key Value) :=
  slotGen key (fun _ inherited => (inherited ()).map change)

def Record.compute {Key : Type} {Value : Key → Type} [DecidableEq Key]
    (key : Key) (calculate : Record Key Value → Value key) :
    Proto (Record Key Value) (Record Key Value) (Record Key Value) :=
  slotGen key (fun self _ => some (calculate self))

/-- Close a composed record prototype with one shared final self. -/
unsafe def Record.instantiate {Key : Type} {Value : Key → Type}
    (prototype : Proto (Record Key Value) (Record Key Value)
      (Record Key Value)) (base : Record Key Value) : Record Key Value :=
  (sharedFix fun self =>
    prototype { lookup := fun key => self.get.lookup key } base).get

end LeanPoo.Prototype
