import LeanPoo.Object.Ranked

/-!
Incremental evaluation for a finite, dependency-checked object. The new plan
remains the sole slot evaluator. An impact report only decides which previously
evaluated values can be carried to its fixed-point instance.
-/

namespace LeanPoo.Object

universe u v

/-- A checked reverse dependency footprint for an edit at `roots`. -/
structure Impact {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (spec : Dependencies Key Value plan)
    (roots : List Key) where
  affected : Key → Bool
  rootsIncluded : ∀ key, key ∈ roots → affected key = true
  closed : ∀ key dependency, affected key = false →
    dependency ∈ spec.reads key → affected dependency = false

/-- If the finite propagation check fails, no cache entry is reused. -/
inductive ImpactError (Key : Type u) where
  | notClosed (keys : List Key)
  deriving Repr

/-- Propagate changed roots through the dependency-first schedule and check
that no unmarked slot reads a marked slot. -/
def Scheduled.impact {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} {spec : Dependencies Key Value plan}
    (scheduled : Scheduled spec) (roots : List Key) :
    Except (ImpactError Key) (Impact spec roots) := do
  let propagated := scheduled.order.foldl (fun seen key =>
    if (roots.contains key) ||
        (spec.reads key).any (fun dependency => seen.contains dependency) then
      seen.insert key
    else seen) ({} : Std.HashSet Key)
  let affected := fun key => (roots.contains key) || propagated.contains key
  if checked : spec.keys.all (fun key =>
      if affected key then true
      else (spec.reads key).all (fun dependency => !affected dependency)) = true then
    return {
      affected
      rootsIncluded := by
        intro key membership
        simp [affected, membership]
      closed := by
        intro key dependency unaffected membership
        have keyChecked := List.all_eq_true.mp checked key
          (spec.supported key dependency membership)
        simp [unaffected] at keyChecked
        exact keyChecked dependency membership }
  else
    throw (.notClosed spec.keys)

/-- An unmarked value is unchanged when its resolver body is unchanged at
the old self and every declared self dependency is also unmarked. -/
theorem Scheduled.stableState {Key : Type u} {Value : Key → Type v}
    {oldPlan newPlan : Plan Key Value}
    {spec : Dependencies Key Value newPlan}
    (scheduled : Scheduled spec) (roots : List Key)
    (impact : Impact spec roots)
    (current : Instance Key Value oldPlan)
    (next : Instance Key Value newPlan)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state) :
    ∀ key, impact.affected key = false →
      current.state key = next.state key := by
  have stableAtRank : ∀ n, ∀ key,
      scheduled.ranked.rank key = n → impact.affected key = false →
        current.state key = next.state key := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro key atRank unaffected
        have depsEqual : ∀ dependency, dependency ∈ spec.reads key →
            current.state dependency = next.state dependency := by
          intro dependency membership
          have lower := scheduled.edgeLower key dependency membership
          rw [atRank] at lower
          exact ih (scheduled.ranked.rank dependency) lower dependency rfl
            (impact.closed key dependency unaffected membership)
        have unmodified : key ∉ roots := by
          intro membership
          have included := impact.rootsIncluded key membership
          simp [unaffected] at included
        calc
          current.state key = oldPlan.resolve key current.state :=
            (current.agrees key).symm
          _ = newPlan.resolve key current.state := sameResolver key unmodified
          _ = newPlan.resolve key next.state :=
            spec.dependsOnlyOn key current.state next.state depsEqual
          _ = next.state key := next.agrees key
  intro key unaffected
  exact stableAtRank (scheduled.ranked.rank key) key rfl unaffected

/-- Transfer evaluated values outside the checked impact set. Misses and
affected slots follow the new resolver's ordinary cache path. -/
def Scheduled.rebaseCache {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Plan Key Value}
    {spec : Dependencies Key Value newPlan}
    (scheduled : Scheduled spec) (roots : List Key)
    (impact : Impact spec roots)
    (current : Instance Key Value oldPlan)
    (next : Instance Key Value newPlan)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state)
    (keys : List Key)
    (cache : Cache (current.prepare keys) current.state) :
    Cache (next.prepare keys) next.state :=
  cache.rebase (next.prepare keys) next.state
    (fun key => impact.affected key = false) (by
      intro key unaffected
      rw [(current.prepare keys).resolve_sound,
        (next.prepare keys).resolve_sound]
      change oldPlan.resolve key current.state =
        newPlan.resolve key next.state
      rw [current.agrees key, next.agrees key]
      exact scheduled.stableState roots impact current next sameResolver
        key unaffected)

inductive RevisionError (Key : Type u) where
  | dependency (error : DependencyError Key)
  | impact (error : ImpactError Key)
  deriving Repr

/-- A new certified fixed point, its checked impact, and the values retained
from the old cache. The instance is derived from the schedule rather than
stored as a second source of truth. -/
structure Revision {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (spec : Dependencies Key Value plan)
    (roots keys : List Key) where
  scheduled : Scheduled spec
  impact : Impact spec roots
  cache : Cache
    ((scheduled.ranked.instantiate).prepare keys)
    (scheduled.ranked.instantiate).state

def Revision.instanceValue {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} {spec : Dependencies Key Value plan}
    {roots keys : List Key} (revision : Revision spec roots keys) :
    Instance Key Value plan :=
  revision.scheduled.ranked.instantiate

/-- A finite write footprint for the next resolved state. It includes direct
edits even when their keys are not in the declared finite support. -/
def Revision.touched {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} {spec : Dependencies Key Value plan}
    {roots keys : List Key} (revision : Revision spec roots keys) : List Key :=
  roots ++ spec.keys.filter revision.impact.affected

/-- Values outside the finite write footprint agree across the two fixed
points. Keys outside the declared support have no self reads by `supported`. -/
theorem Revision.stableOutside {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] [DecidableEq Key]
    {oldPlan newPlan : Plan Key Value}
    {spec : Dependencies Key Value newPlan}
    {roots keys : List Key} (revision : Revision spec roots keys)
    (current : Instance Key Value oldPlan)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state)
    (key : Key) (untouched : key ∉ revision.touched) :
    current.state key = revision.instanceValue.state key := by
  have notRoot : key ∉ roots := by
    intro membership
    exact untouched (List.mem_append.mpr (Or.inl membership))
  by_cases listed : key ∈ spec.keys
  · have notAffected : revision.impact.affected key = false := by
      cases affected : revision.impact.affected key with
      | false => rfl
      | true =>
          have inFilter : key ∈ spec.keys.filter revision.impact.affected :=
            List.mem_filter.mpr ⟨listed, affected⟩
          exact False.elim (untouched (List.mem_append.mpr (Or.inr inFilter)))
    exact revision.scheduled.stableState roots revision.impact
      current revision.instanceValue sameResolver key notAffected
  · have noReads : ∀ dependency, dependency ∈ spec.reads key → False := by
      intro dependency membership
      exact listed (spec.supported key dependency membership)
    calc
      current.state key = oldPlan.resolve key current.state :=
        (current.agrees key).symm
      _ = newPlan.resolve key current.state := sameResolver key notRoot
      _ = newPlan.resolve key revision.instanceValue.state :=
        spec.dependsOnlyOn key current.state revision.instanceValue.state
          (by intro dependency membership; exact False.elim (noReads dependency membership))
      _ = revision.instanceValue.state key := revision.instanceValue.agrees key

/-- Revise a checked finite-dependency object in one operation: construct
the next fixed point, propagate changed roots, and transfer only values
proved stable. -/
def Dependencies.revise {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Plan Key Value}
    (spec : Dependencies Key Value newPlan)
    (roots : List Key)
    (current : Instance Key Value oldPlan)
    (keys : List Key)
    (cache : Cache (current.prepare keys) current.state)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state) :
    Except (RevisionError Key) (Revision spec roots keys) :=
  match spec.scheduleRanked with
  | .error error => .error (.dependency error)
  | .ok scheduled =>
      match scheduled.impact roots with
      | .error error => .error (.impact error)
      | .ok impact => .ok {
          scheduled
          impact
          cache := scheduled.rebaseCache roots impact current
            scheduled.ranked.instantiate sameResolver keys cache
        }

end LeanPoo.Object
