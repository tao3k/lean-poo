import LeanPoo.Object.Resolve

/-!
Proof objects are the project-owned layer above the POO/C4 translation.
Their state is dependently typed, so a key determines the type of its value.
-/

namespace LeanPoo.Proof

universe u v

abbrev State (Key : Type u) (Value : Key → Type v) :=
  (key : Key) → Value key

/-- An obligation states exactly which keys suffice to transport its proof. -/
structure Obligation (Key : Type u) (Value : Key → Type v) where
  dependencies : List Key
  holds : State Key Value → Prop
  stable : ∀ before after : State Key Value,
    (∀ key, key ∈ dependencies → before key = after key) →
    holds before → holds after

structure ProofObject (Key : Type u) (Value : Key → Type v) where
  state : State Key Value
  obligations : List (Obligation Key Value)

/-- A certificate covers every obligation owned by this object. -/
def Certificate (object : ProofObject Key Value) : Prop :=
  ∀ obligation, obligation ∈ object.obligations → obligation.holds object.state

end LeanPoo.Proof
