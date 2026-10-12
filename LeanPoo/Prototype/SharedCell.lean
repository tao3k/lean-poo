/-! The one constructor program used by both native and model backends.
Primitive effects remain explicit; this module assumes no law about IO. -/
namespace LeanPoo.Prototype.SharedCell

inductive Target where
  | unavailable | result
  deriving Repr, BEq, DecidableEq

/-- Completed primitive operations and closure entry/return observations.
`forceResult`/`forceSelf` acknowledge a completed native get, after publication.
`verify` contains a native pointer readback, treated as untrusted data. -/
inductive Event where
  | mkUnavailable | mkRef | mkSelf | mkResult
  | setRef (target : Target)
  | beginResult | returnResult | forceResult
  | beginSelf | getRef (target : Target) | returnSelf | forceSelf
  | verify (confirmed : Bool)
  deriving Repr, BEq, DecidableEq

structure Operations (M : Type → Type) (Ref Delay : Type) where
  unavailable : M Delay
  mkRef : Delay → M Ref
  mkSelf : Ref → M Delay
  mkResult : Delay → M Delay
  setRef : Ref → Delay → M Unit

/-- Allocation, delayed self, delayed result, then installation. Neither
thunk is forced by this constructor. The native backend calls this definition. -/
@[inline] def tie [Monad M] (ops : Operations M Ref Delay) : M Delay := do
  let unavailable ← ops.unavailable
  let cell ← ops.mkRef unavailable
  let self ← ops.mkSelf cell
  let result ← ops.mkResult self
  ops.setRef cell result
  return result

def construction : List Event :=
  [.mkUnavailable, .mkRef, .mkSelf, .mkResult, .setRef .result]

end LeanPoo.Prototype.SharedCell
