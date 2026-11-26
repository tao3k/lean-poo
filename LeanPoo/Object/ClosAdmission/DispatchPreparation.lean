-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.CandidateShape
import LeanPoo.Object.ClosAdmission.StandardRecipe

namespace LeanPoo.Object.ClosAdmission.DispatchPreparation

open LeanPoo.Object.ClosQualifiers
open LeanPoo.Object.ClosAdmission.CandidateShape (rankedLe)
open LeanPoo.Object.ClosAdmission.StandardRecipe (group prepare select)

/-- The cold Scheme preparation filters, stably sorts and groups the
eligible methods. With a stock order-preserving selection, the published
candidate rank and normalized group layout can both precede the live
argument tests. An applicability hook that reorders the candidates does
not satisfy the order-preserving premise. -/
theorem staged_recipe_eq_cold
    (precedence : List Nat) (distance : Method → List Nat)
    (declarations : List (Method × Spelling)) (live : Method → Bool) :
    select
      (prepare (group (declarations.mergeSort (fun a b =>
        rankedLe precedence (distance a.1) (distance b.1))))) live =
    prepare
      (group ((declarations.filter fun row => live row.1).mergeSort (fun a b =>
        rankedLe precedence (distance a.1) (distance b.1)))) := by
  rw [StandardRecipe.selection_preserves_preparation]
  exact congrArg (fun rows => prepare (group rows))
    (CandidateShape.candidate_filter_in_c4_order precedence (fun row => distance row.1)
      (fun row => live row.1) declarations)


open LeanPoo.Object.ClosAdmission.CandidateShape
  (Candidate capturedRows referenceRows published_ranked_candidates_eq_cold)

/-- One refinement statement from C4 distances and live eql guards to the
standard effective-method recipe. The observable reads that provide
these inputs remain ordered by ObservationResume. -/
theorem c4_recipe_eq_cold [BEq Key] (eqv : Value → Value → Bool) (actual : List Value)
    (rows : List (Candidate (Method × Spelling) Key Value))
    (arity : ∀ row ∈ rows, row.required.length ≤ actual.length)
    (precedence : List Nat) :
    let order := fun (a b : Candidate (Method × Spelling) Key Value × List Nat) =>
      rankedLe precedence a.2 b.2
    let label := fun (row : Candidate (Method × Spelling) Key Value × List Nat) =>
      (row, row.1.method.2)
    select (prepare (group (((capturedRows rows).mergeSort order).map label)))
        (fun row => row.1.guardAccepts eqv actual) =
      prepare (group (((referenceRows eqv actual rows).mergeSort order).map label)) := by
  dsimp only
  rw [StandardRecipe.selection_preserves_preparation, List.filter_map]
  exact congrArg (fun ordered => prepare (group (ordered.map fun row => (row, row.1.method.2))))
    (published_ranked_candidates_eq_cold eqv actual rows arity precedence)

end LeanPoo.Object.ClosAdmission.DispatchPreparation
