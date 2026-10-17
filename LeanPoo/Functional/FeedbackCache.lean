import LeanPoo.Functional.ConstructionCache
import LeanPoo.Prototype.FeedbackClosure

/-! Cache nodes may contain whole certified feedback groups. Cycles stay inside
groups; existing ranked DAG invalidation governs inter-group reuse. -/
namespace LeanPoo.Functional.FeedbackCache
open Prototype.Generalized GeneralizedGraph ConstructionCache
variable {Input Raw Cooked : Type}
/-- A first-order cache value retains the actual closure and EVERY residual for
its exact input-indexed component family. No serialized proof token is admitted. -/
structure Group (family : Input → List (Fragment Raw Cooked)) (cook : Raw → Cooked) (base : Raw) where
  input : Input
  result : BoundedClosed (fragmentProtocol cook) (family input) base
  equations : ∀ part ∈ family input, part.feedbackEquation cook base result.closed.raw
/-- Rebuild a dirty group in full with the existing controlled feedback search. -/
def closeGroup [DecidableEq Raw] (family : Input → List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base : Raw) (input : Input) (seed : Raw) (budget : Nat) : Except String (Group family cook base) :=
  match found : closeFeedback (family input) cook base seed budget with
  | .error message => .error message
  | .ok result => .ok ⟨input,result,fun part member => closeFeedback_equations _ _ _ _ _ _ found part member⟩
/-- A retained group still supplies its SAME whole raw fixed-point equation. -/
theorem Group.fixed {family : Input → List (Fragment Raw Cooked)} {cook : Raw → Cooked} {base : Raw}
    (group : Group family cook base) :
    (fragmentProtocol cook).step (family group.input) group.result.closed.raw base = group.result.closed.raw :=
  group.result.closed.fixed
/-- Actual dirty-group construction never exceeds its explicit raw search budget. -/
theorem closeGroup_bound [DecidableEq Raw] (family : Input → List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base : Raw) (input : Input) (seed : Raw) (budget : Nat) (group : Group family cook base)
    (accepted : closeGroup family cook base input seed budget = .ok group) : group.result.steps ≤ budget := by
  unfold closeGroup at accepted
  split at accepted
  · contradiction
  · rename_i result found
    cases accepted
    exact closeFeedback_bound _ _ _ _ _ _ found

variable {Key : Type} {Value : Key → Type} [DecidableEq Key]
/-- Transitive invalidation includes both branches of a shared dependency hub.
It does not attempt to topologically order individual nodes inside a cycle. -/
theorem shared_invalidates {spec : Declaration Key Value} (scheduled : Scheduled spec)
    (changed : Key → Bool) (shared left right : Key)
    (leftReads : shared ∈ spec.reads left) (rightReads : shared ∈ spec.reads right)
    (dirty : scheduled.invalidates changed shared = true) :
    scheduled.invalidates changed left = true ∧ scheduled.invalidates changed right = true :=
  ⟨scheduled.invalidates_reader changed left shared leftReads dirty,
   scheduled.invalidates_reader changed right shared rightReads dirty⟩
/-- A clean cached slot is exactly the newly closed reference value under actual
resolver equality and declared dependency invalidation, not sampled observations. -/
theorem retained_slot {old spec : Declaration Key Value} (scheduled : Scheduled spec) (cache : Cache old)
    (changed : Key → Bool)
    (unchanged : ∀ key, changed key = false → ∀ self, spec.resolve key self = old.resolve key self)
    (key : Key) (clean : scheduled.invalidates changed key = false) :
    cache.closed.raw key = scheduled.closed.raw key :=
  scheduled.unaffected changed (fun key safe self => (unchanged key safe self).symm) cache.closed key clean
/-- Joint approval runs on the exact materialized cache, even when every slot was
retained. Construction failures remain in the existing materializer's error path. -/
def admitCache {spec : Declaration Key Value} (candidate : Cache spec) (admit : Cache spec → Bool) :
    Except String (Cache spec) :=
  if admit candidate then .ok candidate else .error "joint feedback cache approval refused"
/-- No unchanged-cache shortcut can certify current approval automatically. -/
theorem admitCache_approved {spec : Declaration Key Value} (candidate result : Cache spec)
    (admit : Cache spec → Bool) (accepted : admitCache candidate admit = .ok result) :
    result = candidate ∧ admit result = true := by
  unfold admitCache at accepted
  split at accepted
  · rename_i approved
    cases accepted; exact ⟨rfl,approved⟩
  · contradiction
end LeanPoo.Functional.FeedbackCache
