-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.PublishedDispatch

namespace LeanPoo.Object.ClosAdmission.ObservationResume
open LeanPoo.Object.ClosAdmission.PublishedDispatch

abbrev Select (n : Nat) (Value Runtime Recipe Event Failure : Type) :=
  Stage n Value Runtime Recipe Event Failure → World n Value Runtime → Recipe

/-- An observation list is the list of actual issued reads. The result of
one predicate cannot short-circuit the effect of reading its successors. -/
def observeAll {M : Type → Type} [Monad M] (read : Query → M Bool)
    (queries : List Query) : M Bool := do
  let answers ← queries.mapM read
  pure (answers.all id)

private def exampleRead (query : Nat) : StateM (List Nat) Bool := do
  modify fun visited => visited ++ [query]
  pure (query != 0)

-- An eql mismatch on the first argument must still demand the later slot.
#guard Id.run ((observeAll exampleRead [0, 1, 2]).run []) == (false, [0, 1, 2])

/-- Two pieces of a call compose through the world left by the first.
This cut is where a stale publication resumes: an earlier refusal returns
the original outcome and a completed prefix is not executed again. -/
theorem run_append (select : Select n Value Runtime Recipe Event Failure)
    (prefixStages suffix : List (Stage n Value Runtime Recipe Event Failure))
    (world : World n Value Runtime) :
    run select (prefixStages ++ suffix) world =
      let finished := run select prefixStages world
      match finished.result with
      | .error _ => finished
      | .ok () =>
        let next := run select suffix finished.world
        { next with events := finished.events ++ next.events } := by
  induction prefixStages generalizing world with
  | nil =>
    simp [run]
  | cons stage rest ih =>
    simp only [List.cons_append, run]
    generalize stage.perform (select stage world) world = observed
    cases h : observed.result with
    | error cause => simp [h]
    | ok value =>
      cases value
      rw [ih]
      cases hNext : (run select rest observed.world).result with
      | error cause => simp [hNext]
      | ok value =>
        cases value
        simp [hNext, List.append_assoc]

/-- Route lookup may change pure preparation. Independently authenticated
work at an effect boundary ignores the result of that lookup. -/
def boundary (owner : Fin n) (initial : Recipe)
    (action : World n Value Runtime → Outcome (World n Value Runtime) Event Failure) :
    Stage n Value Runtime Recipe Event Failure :=
  { owner := owner, support := [], prepare := fun _ => initial,
    perform := fun _ world => action world }

/-- After the callback, the guard uses the new world and can refuse. The
continuation preserves all three event segments regardless of plan hits. -/
theorem independent_postcheck_refusal
    (select : Select n Value Runtime Recipe Event Failure)
    (owner : Fin n) (initial : Recipe)
    (guard action : World n Value Runtime → Outcome (World n Value Runtime) Event Failure)
    (before after afterCheck : World n Value Runtime)
    (preReads callReads postReads : List Event) (failure : Failure)
    (pre : guard before = ⟨before, .ok (), preReads⟩)
    (returned : action before = ⟨after, .ok (), callReads⟩)
    (post : guard after = ⟨afterCheck, .error failure, postReads⟩)
    (remaining : List (Stage n Value Runtime Recipe Event Failure)) :
    run select (boundary owner initial guard :: boundary owner initial action ::
                boundary owner initial guard :: remaining) before =
      ⟨afterCheck, .error failure, preReads ++ callReads ++ postReads⟩ := by
  simp [run, boundary, pre, returned, post, List.append_assoc]

/-- A prefix that has crossed a callback is kept verbatim. Guarded reuse
in the remaining stages preserves the result and the exact issued-read
suffix of fresh preparation in the callback's returned world. -/
theorem resume_eq_cold
    (read : Stage n Value Runtime Recipe Event Failure → World n Value Runtime →
      Option (Published n Recipe))
    (prefixStages suffix : List (Stage n Value Runtime Recipe Event Failure))
    (world : World n Value Runtime)
    (valid : ∀ stage ∈ suffix, ∀ w saved, read stage w = some saved →
      current stage w saved → saved.plan = cold stage w) :
    let finished := run cold prefixStages world
    (match finished.result with
    | .error _ => finished
    | .ok () =>
      let next := run (fun stage w => (choose stage w (read stage w)).1) suffix finished.world
      { next with events := finished.events ++ next.events }) =
      run cold (prefixStages ++ suffix) world := by
  rw [run_append]
  exact congrArg (fun next =>
    let finished := run cold prefixStages world
    match finished.result with
    | .error _ => finished
    | .ok () => {next with events := finished.events ++ next.events})
    (run_eq_cold read suffix (run cold prefixStages world).world valid)

end LeanPoo.Object.ClosAdmission.ObservationResume
