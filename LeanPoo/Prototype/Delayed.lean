import LeanPoo.Prototype.Compose

/-!
POOF's delayed prototype construction, expressed with Lean's `Thunk`.
This supports lazy fixed points whose instance is not a function type.
-/

namespace LeanPoo.Prototype

universe u v w

/-- The final self and inherited computation are both delayed. -/
abbrev DelayedProto (Self : Type u) (Parent : Type v)
    (Result : Type w) := Thunk Self → Thunk Parent → Result

def DelayedProto.identity : DelayedProto Self α α :=
  fun _ inherited => inherited.get

/-- A terminal delayed prototype never forces its inherited computation. -/
def DelayedProto.constant (value : Result) : DelayedProto Self Parent Result :=
  fun _ _ => value

/-- Compose without forcing the parent when the child overrides it. -/
def DelayedProto.compose (child : DelayedProto Self Middle Result)
    (parent : DelayedProto Self Parent Middle) :
    DelayedProto Self Parent Result :=
  fun self inherited =>
    child self (Thunk.mk fun _ => parent self inherited)

/-- An inheritance chain whose intermediate value types are checked by Lean. -/
inductive DelayedProto.Chain (Self : Type u) :
    Type v → Type v → Type (max u (v + 1)) where
  | nil : Chain Self α α
  | cons : DelayedProto Self Middle Result → Chain Self Parent Middle →
      Chain Self Parent Result

/-- Join chains only when the inner result matches the outer parent type. -/
def DelayedProto.Chain.append :
    Chain Self Middle Result → Chain Self Parent Middle →
      Chain Self Parent Result
  | .nil, parent => parent
  | .cons child tail, parent => .cons child (tail.append parent)

/-- Interpret a typed chain using the single delayed composition operation. -/
def DelayedProto.Chain.toProto :
    Chain Self Parent Result → DelayedProto Self Parent Result
  | .nil => DelayedProto.identity
  | .cons child tail => DelayedProto.compose child tail.toProto

def DelayedProto.Chain.ofList
    (prototypes : List (DelayedProto Self α α)) : Chain Self α α :=
  prototypes.foldr Chain.cons Chain.nil

/-- Tie one shared delayed final self to a prototype whose result has that
type. Lean's kernel does not accept this general recursive value, so the
executable thunk knot is explicitly `unsafe`; its types remain checked. -/
unsafe def DelayedProto.instantiate
    {Self Parent : Type}
    (prototype : DelayedProto Self Parent Self) (base : Thunk Parent) :
    Thunk Self :=
  sharedFix fun self => prototype self base

/-- Instantiate a precedence-ordered list in one delayed fixed point. -/
def DelayedProto.composeAll
    (prototypes : List (DelayedProto Self α α)) : DelayedProto Self α α :=
  (DelayedProto.Chain.ofList prototypes).toProto

/-- Close a typed delayed chain whose result is the final self type. -/
unsafe def DelayedProto.Chain.instantiate
    {Self Parent : Type}
    (chain : Chain Self Parent Self) (base : Thunk Parent) : Thunk Self :=
  DelayedProto.instantiate chain.toProto base

unsafe def DelayedProto.instantiateAll
    {α : Type} (prototypes : List (DelayedProto α α α))
    (base : Thunk α) : Thunk α :=
  DelayedProto.instantiate (DelayedProto.composeAll prototypes) base

end LeanPoo.Prototype
