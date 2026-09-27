/-!
The four slot-spec forms are translated from François-René Rideau's
Gerbil-POO object.ss.
The upstream implementation uses Apache-2.0.
-/

namespace LeanPoo.Prototype

universe u v

/-- A delayed inherited computation. Keeping it delayed preserves the
Gerbil-POO distinction between overriding a slot and requesting its parent. -/
abbrev Next (α : Type v) := Unit → α

/-- An open method receives the final self and a delayed inherited result. -/
abbrev Method (Self : Type u) (α : Type v) := Self → Next α → α

def Method.identity : Method Self α := fun _ inherited => inherited ()

/-- Child methods may choose whether to request their parent's result. -/
def Method.compose (child parent : Method Self α) : Method Self α :=
  fun self inherited => child self (fun _ => parent self inherited)

theorem Method.compose_identity_left (method : Method Self α) :
    Method.compose Method.identity method = method := by
  funext self inherited
  rfl

theorem Method.compose_identity_right (method : Method Self α) :
    Method.compose method Method.identity = method := by
  funext self inherited
  rfl

theorem Method.compose_assoc (outer middle inner : Method Self α) :
    Method.compose (Method.compose outer middle) inner =
      Method.compose outer (Method.compose middle inner) := by
  funext self inherited
  rfl

/-- The semantic target of Gerbil-POO's object/slot-spec syntax normalization. -/
inductive SlotSpec (Self : Type u) (α : Type v) where
  | constant (value : α)
  | thunk (value : Next α)
  | self (compute : Self → α)
  | computed (compute : Self → Next α → α)

/-- One interpretation owns all slot-spec forms. -/
def SlotSpec.eval (spec : SlotSpec Self α) (self : Self)
    (next : Next α) : α :=
  match spec with
  | .constant value => value
  | .thunk value => value ()
  | .self compute => compute self
  | .computed compute => compute self next

def SlotSpec.toMethod (spec : SlotSpec Self α) : Method Self α :=
  fun self inherited => spec.eval self inherited

/-- The common inherited-value modifier represented by the computed form. -/
def SlotSpec.modify (f : α → α) : SlotSpec Self α :=
  .computed (fun _ next => f (next ()))

/-- The inherited instance method is selected by the class's C4 slot chain.
The receiver is supplied only when the resulting method is called, so it may
belong to a subclass of the class that contributed this specification. -/
abbrev NextInstanceMethod (Receiver : Type u) (Result : Type v) :=
  Receiver → Option Result

/-- Focus an open class specification onto an instance method. The class
`self` is deliberately unused; method dispatch uses the eventual receiver. -/
def SlotSpec.instanceMethod {ClassSelf : Type} {Receiver : Type u}
    {Result : Type v}
    (body : NextInstanceMethod Receiver Result → Receiver → Result) :
    SlotSpec ClassSelf (Option (Receiver → Result)) :=
  .computed fun _ inherited =>
    let parent := Thunk.mk inherited
    some fun receiver =>
      body (fun target => parent.get.map (fun method => method target)) receiver

/-- A base method does not request an inherited method. -/
def SlotSpec.baseInstanceMethod {ClassSelf : Type} {Receiver : Type u}
    {Result : Type v} (body : Receiver → Result) :
    SlotSpec ClassSelf (Option (Receiver → Result)) :=
  .constant (some body)

theorem SlotSpec.instanceMethod_eval {ClassSelf : Type}
    {Receiver : Type u} {Result : Type v}
    (body : NextInstanceMethod Receiver Result → Receiver → Result)
    (self : ClassSelf)
    (inherited : Next (Option (Receiver → Result)))
    (receiver : Receiver) :
    ((SlotSpec.instanceMethod body).eval self inherited).map
        (fun method => method receiver) =
      some (body (fun target => (Thunk.mk inherited).get.map
        (fun method => method target)) receiver) := rfl

theorem SlotSpec.baseInstanceMethod_eval {ClassSelf : Type}
    {Receiver : Type u} {Result : Type v}
    (body : Receiver → Result) (self : ClassSelf)
    (inherited : Next (Option (Receiver → Result)))
    (receiver : Receiver) :
    ((SlotSpec.baseInstanceMethod body).eval self inherited).map
      (fun method => method receiver) = some (body receiver) := rfl

end LeanPoo.Prototype
