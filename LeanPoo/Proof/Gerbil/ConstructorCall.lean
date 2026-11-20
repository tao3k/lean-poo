import Std

namespace ConstructorCall

-- Closed no-argument convenience calls only. Values model procedure identities;
-- default/absent denotes the native binder marker, not a fabricated new default.
inductive Key where
  | size | seed | test | hash | lock | check | weakKeys | weakValues
  deriving DecidableEq, Repr

inductive Value where
  | absent | procedure (identity : Nat)
  deriving DecidableEq, Repr

abbrev Packet := Key → Value
abbrev Arguments := List (Key × Value)

def lookup (args : Arguments) (key : Key) : Value :=
  match args with
  | [] => .absent
  | (name, value) :: rest => if name = key then value else lookup rest key

def symbolicArgs (eqIdentity hashIdentity : Nat) : Arguments :=
  [(.test, .procedure eqIdentity), (.hash, .procedure hashIdentity)]

def identityArgs (eqIdentity : Nat) : Arguments := [(.test, .procedure eqIdentity)]

def symbolicPacket (eqIdentity hashIdentity : Nat) : Packet := fun key =>
  match key with
  | .test => .procedure eqIdentity
  | .hash => .procedure hashIdentity
  | _ => .absent

def identityPacket (eqIdentity : Nat) : Packet := fun key =>
  match key with
  | .test => .procedure eqIdentity
  | _ => .absent

theorem symbolic_binding_exact (eqIdentity hashIdentity : Nat) :
    lookup (symbolicArgs eqIdentity hashIdentity ++ []) =
      symbolicPacket eqIdentity hashIdentity := by
  funext key
  cases key <;> rfl

theorem identity_binding_exact (eqIdentity : Nat) :
    lookup (identityArgs eqIdentity ++ []) = identityPacket eqIdentity := by
  funext key
  cases key <;> rfl

-- Constructor effects are arbitrary: seed draw, adapter construction, callbacks,
-- refusals, and fresh result identity remain owned by that SAME native body.
-- Only the closed packet materialization is erased as pure temporary work.
abbrev Action (State Error Result : Type) := State → Except Error Result × State

def throughHelper (constructor : Packet → Action S E V) (args : Arguments) : Action S E V :=
  constructor (lookup (args ++ []))

theorem symbolic_call_exact (constructor : Packet → Action S E V)
    (eqIdentity hashIdentity : Nat) :
    throughHelper constructor (symbolicArgs eqIdentity hashIdentity) =
      constructor (symbolicPacket eqIdentity hashIdentity) := by
  unfold throughHelper
  rw [symbolic_binding_exact]

theorem identity_call_exact (constructor : Packet → Action S E V) (eqIdentity : Nat) :
    throughHelper constructor (identityArgs eqIdentity) =
      constructor (identityPacket eqIdentity) := by
  unfold throughHelper
  rw [identity_binding_exact]

-- Supplying an explicit seed or default is a different packet. Never introduce
-- seed:=0 or eager RNG work as a shortcut for the native default argument.
example : symbolicPacket 1 2 .seed = .absent := rfl
example : symbolicPacket 1 2 .size = .absent := rfl
example : symbolicPacket 1 2 .test = .procedure 1 := rfl
example : symbolicPacket 1 2 .hash = .procedure 2 := rfl

#print axioms symbolic_binding_exact
#print axioms identity_binding_exact
#print axioms symbolic_call_exact
#print axioms identity_call_exact

end ConstructorCall
