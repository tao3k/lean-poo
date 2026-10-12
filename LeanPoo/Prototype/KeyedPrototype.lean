import LeanPoo.Prototype.Object

/-! The paper's prototype/function plus key-list representation. -/
namespace LeanPoo.Prototype.KeyedPrototype

abbrev Slot (Key : Type) := Sum Key Unit
abbrev Value (Values : Key → Type) : Slot Key → Type
  | .inl key => Values key
  | .inr _ => List Key
abbrev Rec (Values : Key → Type) := Record (Slot Key) (Value Values)

structure Definition (Key : Type) (Values : Key → Type) where
  layer : DelayedProto (Rec Values) (Rec Values) (Rec Values)
  keys : List Key

/-- Retain source key lists, including duplicates; this is not a set union. -/
def compose (child parent : Definition Key Values) : Definition Key Values :=
  ⟨DelayedProto.compose child.layer parent.layer, child.keys ++ parent.keys⟩

def slot [DecidableEq Key] (key : Key) (value : Values key) : Definition Key Values :=
  ⟨Object.recordSlotGen (.inl key) (fun _ _ => some value), [key]⟩

def expose {Key : Type} {Values : Key → Type} [DecidableEq Key] (keys : List Key) :
    DelayedProto (Rec Values) (Rec Values) (Rec Values) :=
  Object.recordSlotGen (.inr ()) (fun _ _ => some keys)

/-- Expose keys through the same instance slot interface as ordinary values.
With allowOverride, source layers may intercept the keys slot. -/
def Definition.withKeys [DecidableEq Key] (definition : Definition Key Values)
    (allowOverride : Bool := false) : DelayedProto (Rec Values) (Rec Values) (Rec Values) :=
  if allowOverride then DelayedProto.compose definition.layer (expose definition.keys)
  else DelayedProto.compose (expose definition.keys) definition.layer

unsafe def instantiate [DecidableEq Key] (definition : Definition Key Values)
    (base : Rec Values := Record.empty) (allowOverride : Bool := false) : Rec Values :=
  (DelayedProto.instantiate (definition.withKeys allowOverride) (Thunk.pure base)).get

end LeanPoo.Prototype.KeyedPrototype
