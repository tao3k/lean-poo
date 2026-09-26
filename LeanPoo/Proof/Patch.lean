import LeanPoo.Proof.Types

namespace LeanPoo.Proof

universe u v

/-- A patch declares its write footprint and proves a frame property. -/
structure Patch (Key : Type u) (Value : Key → Type v) where
  apply : State Key Value → State Key Value
  touched : List Key
  frame : ∀ state key, key ∉ touched → apply state key = state key
  obligations : List (Obligation Key Value)

/-- Override one typed key. The frame proof is derived from key inequality. -/
def Patch.set [DecidableEq Key] (key : Key) (value : Value key)
    (obligations : List (Obligation Key Value) := []) : Patch Key Value where
  apply := fun state query =>
    if same : query = key then same.symm ▸ value else state query
  touched := [key]
  frame := by
    intro state query untouched
    have different : query ≠ key := by
      intro same
      exact untouched (by simp [same])
    simp [different]
  obligations := obligations

/-- Append applies the right patch and carries both sets of obligations. -/
def append (object : ProofObject Key Value) (patch : Patch Key Value) :
    ProofObject Key Value :=
  ⟨patch.apply object.state, object.obligations ++ patch.obligations⟩

/-- The second patch observes and modifies the state produced by the first. -/
def Patch.then (first second : Patch Key Value) : Patch Key Value where
  apply := second.apply ∘ first.apply
  touched := first.touched ++ second.touched
  frame := by
    intro state key h
    have h₁ : key ∉ first.touched := by
      intro membership
      exact h (List.mem_append.mpr (Or.inl membership))
    have h₂ : key ∉ second.touched := by
      intro membership
      exact h (List.mem_append.mpr (Or.inr membership))
    change second.apply (first.apply state) key = state key
    calc
      second.apply (first.apply state) key = first.apply state key :=
        second.frame (first.apply state) key h₂
      _ = state key := first.frame state key h₁
  obligations := first.obligations ++ second.obligations

theorem append_then (object : ProofObject Key Value)
    (first second : Patch Key Value) :
    append (append object first) second = append object (first.then second) := by
  cases object
  simp [append, Patch.then, Function.comp_def, List.append_assoc]

end LeanPoo.Proof
