import LeanPoo.Functional.SetAlgebra

/-! Access-policy algebra composes existing table revisions, inverse recovery,
styles and service lenses. This advances the collection proposal's future work. -/
namespace LeanPoo.Examples.SetAlgebra
open Functional.OrderedDictionary

/-- A finite access policy retains an unrelated permission across revisions. -/
def original : Membership Nat := fun key => decide (key = 1 ∨ key = 2 ∨ key = 5)
/-- Duplicate grant intent has ordinary set semantics, not a second write. -/
def grants : Membership Nat := fun key => decide (key = 2 ∨ key = 3 ∨ key = 4)
/-- Explicit revocation overrides grants in the complete policy operation. -/
def revoked : Membership Nat := fun key => decide (key = 2 ∨ key = 4)
/-- The proposed policy is computed by the same union-then-difference chain. -/
def proposed : Membership Nat := combineSet .diff (combineSet .union original grants) revoked

example : (proposed 1, proposed 2, proposed 3, proposed 4, proposed 5) =
    (true, false, true, false, true) := rfl

/-- A finite key inventory covers both policies without enumerating all Nat. -/
theorem outside_same (key : Nat) (outside : key ∉ [1,2,3,4,5]) : original key = proposed key := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  rcases outside with ⟨h1, h2, h3, h4, h5⟩
  simp [original, grants, revoked, proposed, combineSet, SetOperation.choose, h1, h2, h3, h4, h5]

/-- The ordinary table delta is the complete new policy, not a second set delta API. -/
def edits : List (Change Nat Unit) := diffChanges [1,2,3,4,5]
  (membershipTable original) (membershipTable proposed)

/-- Installation preserves all keys, including the unrelated retained permission. -/
theorem installed : applyChanges edits (membershipTable original) = .ok (membershipTable proposed) := by
  apply diff_complete [1,2,3,4,5] (by decide)
  intro key outside
  simp [membershipTable, outside_same key outside]

/-- Reverse installation reuses the original whole-table inverse theorem. -/
example : applyChanges (inverseChanges edits) (membershipTable proposed) = .ok (membershipTable original) :=
  set_revision_inverse edits original proposed installed

/-- A competing revocation of key 2 makes the captured expected membership stale. -/
def winner : Nat → Option Unit := replace (membershipTable original) 2 none
example : applyChanges edits winner = .error 2 := by rfl

/-- Explicit rediscovery permits retry against the winner with unchanged failure rules. -/
example : (applyChanges (diffChanges [1,2,3,4,5] winner (membershipTable proposed)) winner).map
    (fun view => (view 1, view 2, view 3, view 4, view 5)) =
      .ok (some (), none, some (), none, some ()) := by rfl

/-- Classy publication and its failure use the existing complete style engine. -/
example : styleStep .mutable (some winner) (applyChanges edits) =
    (some winner, .error (.callback 2)) := by rfl

/-- A service membership focus preserves unrelated service metadata. -/
example : LeanPoo.Prototype.LensLaws
    (fun service : Membership Nat × String => service.1 2)
    (fun present service => (setMembership service.1 2 present, service.2)) :=
  LeanPoo.Prototype.LensLaws.productFirst.compose (set_membership_lens 2)

/-- Pure access normalization is idempotent at the observable membership boundary. -/
example : combineSet .union proposed proposed = proposed := set_union_idempotent proposed

end LeanPoo.Examples.SetAlgebra
