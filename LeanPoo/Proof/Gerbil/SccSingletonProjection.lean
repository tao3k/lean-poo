-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.ComponentWitness

namespace LeanPoo.Proof.Gerbil.SccSingletonProjection

open LeanPoo.Functional.StrongComponents
open LeanPoo.Functional.ComponentWitness (ranked_singletons_exact)

/-- The low direction bit is preferred when both directions survive capture. -/
def rank (forward : Bool) (owner : Fin n) : Nat :=
  if forward then n - 1 - owner.val else owner.val

abbrev Arc (n : Nat) := Fin n × Fin n

def backward (getRank : Fin n → Nat) (arc : Arc n) : Bool :=
  decide (arc.1 ≠ arc.2 ∧ getRank arc.1 ≤ getRank arc.2)

/-- Compare the captured rows in their original order. An unexpected bad
edge must still be refused, even if capture reported a monotone direction. -/
def firstBad (getRank : Fin n → Nat) (arcs : List (Arc n)) : Option (Arc n) :=
  arcs.find? (backward getRank)

theorem ordinal_check_same_first_refusal
    (oldRank : Fin n → Nat) (forward : Bool)
    (rankRecorded : ∀ key, oldRank key = rank forward key)
    (arcs : List (Arc n)) :
    firstBad oldRank arcs = firstBad (rank forward) arcs := by
  have sameRank : oldRank = rank forward := funext rankRecorded
  rw [sameRank]

def edges (arcs : List (Arc n)) (a b : Fin n) : Bool :=
  decide ((a, b) ∈ arcs)

theorem no_bad_arc_of_pass (getRank : Fin n → Nat) (arcs : List (Arc n))
    (ok : firstBad getRank arcs = none)
    (a b : Fin n) (edge : edges arcs a b = true) (distinct : a ≠ b) :
    getRank b < getRank a := by
  have member : (a, b) ∈ arcs := of_decide_eq_true edge
  have none := List.find?_eq_none.mp ok (a, b) member
  have notBad : ¬ (a ≠ b ∧ getRank a ≤ getRank b) := by
    simpa [backward] using none
  exact Nat.lt_of_not_ge fun ordered => notBad ⟨distinct, ordered⟩

theorem admitted_singletons_exact (forward : Bool) (arcs : List (Arc n))
    (ok : firstBad (rank forward) arcs = none) (a b : Fin n) :
    a = b ↔ Reach (edges arcs) a b ∧ Reach (edges arcs) b a :=
  ranked_singletons_exact (edges arcs) (rank forward)
    (no_bad_arc_of_pass (rank forward) arcs ok) a b

/-- Preserve the representatives exposed by ordinary normalization, including
their order. Under the independent certificate each owner represents itself. -/
theorem singleton_groups_equal_normalized (forward : Bool) (arcs : List (Arc n))
    (ok : firstBad (rank forward) arcs = none)
    (roster : List (Fin n)) (representative : Fin n → Fin n)
    (valid : ∀ a, Reach (edges arcs) a (representative a) ∧
      Reach (edges arcs) (representative a) a) :
    roster.map (fun a => [representative a]) = roster.map (fun a => [a]) := by
  apply List.map_congr_left
  intro a _
  rw [← (admitted_singletons_exact forward arcs ok a (representative a)).mpr (valid a)]

theorem owned_row_edit_cold_exact (forward : Bool) (prior edited : List (Arc n))
    (oldPass : firstBad (rank forward) prior = none)
    (newPass : firstBad (rank forward) edited = none) (a b : Fin n) :
    (Reach (edges prior) a b ∧ Reach (edges prior) b a) ↔
    (Reach (edges edited) a b ∧ Reach (edges edited) b a) :=
  (admitted_singletons_exact forward prior oldPass a b).symm.trans
    (admitted_singletons_exact forward edited newPass a b)

-- Self loops preserve the certificate. The first opposite edge wins.
#guard firstBad (rank false) ([(⟨0, by decide⟩, ⟨0, by decide⟩),
  (⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)] :
    List (Arc 3)) == some (⟨0, by decide⟩, ⟨1, by decide⟩)
#guard (firstBad (rank true) ([(⟨1, by decide⟩, ⟨1, by decide⟩),
  (⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)] :
    List (Arc 3))).isNone

end LeanPoo.Proof.Gerbil.SccSingletonProjection
