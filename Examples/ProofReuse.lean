import LeanPoo.Proof.Reuse

/-! An independent quota change keeps the existing proof about identity.
The caller names the proof's dependency once; `reuse` transports it through
the patch, so the identity theorem is not proved again. -/

namespace LeanPoo.Examples.ProofReuse

inductive Key where
  | identity
  | quota
  deriving DecidableEq

abbrev Value (_ : Key) := Nat

def identityInvariant : LeanPoo.Proof.Obligation Key Value where
  dependencies := [.identity]
  holds := fun state => state .identity = 7
  stable := by
    intro before after same holds
    exact (same .identity (by simp)).symm.trans holds

def original : LeanPoo.Proof.ProofObject Key Value where
  state := fun
    | .identity => 7
    | .quota => 2
  obligations := [identityInvariant]

theorem originalCertified : LeanPoo.Proof.Certificate original := by
  intro obligation member
  have equal : obligation = identityInvariant := by
    simpa [original] using member
  subst obligation
  rfl

def change : LeanPoo.Proof.Patch Key Value :=
  LeanPoo.Proof.Patch.set .quota 5

theorem identityUntouched : LeanPoo.Proof.unaffected identityInvariant change := by
  intro key dependency touched
  have equal : key = .identity := by simpa [identityInvariant] using dependency
  subst key
  simp [change, LeanPoo.Proof.Patch.set] at touched

theorem retained :
    identityInvariant.holds (LeanPoo.Proof.append original change).state :=
  LeanPoo.Proof.reuse original change originalCertified identityInvariant
    (by simp [original]) identityUntouched

theorem revisedCertified :
    LeanPoo.Proof.Certificate (LeanPoo.Proof.append original change) := by
  apply LeanPoo.Proof.close original change originalCertified
  · intro obligation member affected
    have equal : obligation = identityInvariant := by
      simpa [original] using member
    subst obligation
    exact False.elim (affected identityUntouched)
  · intro obligation member
    simp [change, LeanPoo.Proof.Patch.set] at member

#eval (original.state .quota,
  (LeanPoo.Proof.append original change).state .quota)

end LeanPoo.Examples.ProofReuse
