import LeanPoo.Proof.Patch

namespace LeanPoo.Proof

universe u v

/-- An old proof can be reused when the patch leaves every dependency alone. -/
def unaffected (obligation : Obligation Key Value)
    (patch : Patch Key Value) : Prop :=
  ∀ key, key ∈ obligation.dependencies → key ∉ patch.touched

theorem reuse (object : ProofObject Key Value)
    (patch : Patch Key Value) (certificate : Certificate object)
    (obligation : Obligation Key Value)
    (owned : obligation ∈ object.obligations)
    (safe : unaffected obligation patch) :
    obligation.holds (append object patch).state := by
  apply obligation.stable object.state (patch.apply object.state)
  · intro key dependency
    exact (patch.frame object.state key (safe key dependency)).symm
  · exact certificate obligation owned

/-- Only affected old obligations and new obligations need fresh evidence. -/
theorem close (object : ProofObject Key Value)
    (patch : Patch Key Value) (certificate : Certificate object)
    (affected : ∀ obligation, obligation ∈ object.obligations →
      ¬ unaffected obligation patch →
      obligation.holds (append object patch).state)
    (added : ∀ obligation, obligation ∈ patch.obligations →
      obligation.holds (append object patch).state) :
    Certificate (append object patch) := by
  intro obligation membership
  rcases List.mem_append.mp membership with old | fresh
  · by_cases safe : unaffected obligation patch
    · exact reuse object patch certificate obligation old safe
    · exact affected obligation old safe
  · exact added obligation fresh

end LeanPoo.Proof
