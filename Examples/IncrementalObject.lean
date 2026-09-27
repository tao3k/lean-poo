import LeanPoo.Object.Debug
import LeanPoo.Proof.Revision

open LeanPoo

namespace IncrementalObjectExample

inductive Key where
  | source | derived | stableSource | stableDerived
  deriving BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq, Repr

private instance [DecidableEq α] [DecidableEq β] :
    DecidableEq (Except α β) := by
  intro x y
  cases x with
  | error left =>
      cases y with
      | error right => simpa using (inferInstance : Decidable (left = right))
      | ok _ => exact isFalse (by intro equality; cases equality)
  | ok left =>
      cases y with
      | error _ => exact isFalse (by intro equality; cases equality)
      | ok right => simpa using (inferInstance : Decidable (left = right))

private abbrev Values (_ : Key) := Nat

private def graph : C4.Graph :=
  { nodes := [{ name := "Base" },
      { name := "Child", parentOrders := [["Base"]] }] }

private def base (changed : Nat) : Object.Declaration Key Values :=
  Object.Declaration.empty
    |>.withValue .source changed
    |>.withValue .stableSource 7

private def child : Object.Declaration Key Values :=
  Object.Declaration.empty
    |>.withSlot .derived
      (.self fun self => (self .source).map (· + 1))
    |>.withSlot .stableDerived
      (.self fun self => (self .stableSource).map (· * 2))

private def schema (changed : Nat) : Object.Schema Key Values :=
  { graph
    declaration := fun name =>
      if name == "Base" then some (base changed)
      else if name == "Child" then some child else none }

private def plan (changed : Nat) : Object.Plan Key Values :=
  { schema := schema changed
    root := "Child"
    precedence := ["Child", "Base"]
    valid := by
      change C4.linearize graph "Child" = .ok ["Child", "Base"]
      native_decide }

private def dependencies (changed : Nat) :
    Object.Dependencies Key Values (plan changed) :=
  { keys := [.source, .derived, .stableSource, .stableDerived]
    reads := fun key => match key with
      | .derived => [.source]
      | .stableDerived => [.stableSource]
      | _ => []
    supported := by
      intro key dependency membership
      cases key <;> simp
    dependsOnlyOn := by
      intro key left right equal
      cases key with
      | source => rfl
      | stableSource => rfl
      | derived =>
          change (left .source).map (· + 1) =
            (right .source).map (· + 1)
          rw [equal .source (by simp)]
      | stableDerived =>
          change (left .stableSource).map (· * 2) =
            (right .stableSource).map (· * 2)
          rw [equal .stableSource (by simp)] }

private theorem sameResolver (current : Object.Instance Key Values (plan 20))
    (key : Key) (unmodified : key ∉ [.source]) :
    (plan 20).resolve key current.state =
      (plan 30).resolve key current.state := by
  cases key with
  | source => simp at unmodified
  | derived => rfl
  | stableSource => rfl
  | stableDerived => rfl

private def changedRelation : Proof.Obligation Key
    (fun key => Option (Values key)) :=
  { dependencies := [.derived, .source]
    holds := fun state => state .derived = (state .source).map (· + 1)
    stable := by
      intro before after equal holds
      calc
        after .derived = before .derived :=
          (equal .derived (by simp)).symm
        _ = (before .source).map (· + 1) := holds
        _ = (after .source).map (· + 1) := by
          rw [equal .source (by simp)] }

private def stableRelation : Proof.Obligation Key
    (fun key => Option (Values key)) :=
  { dependencies := [.stableDerived, .stableSource]
    holds := fun state => state .stableDerived =
      (state .stableSource).map (· * 2)
    stable := by
      intro before after equal holds
      calc
        after .stableDerived = before .stableDerived :=
          (equal .stableDerived (by simp)).symm
        _ = (before .stableSource).map (· * 2) := holds
        _ = (after .stableSource).map (· * 2) := by
          rw [equal .stableSource (by simp)] }

private theorem changedRelationHolds (changed : Nat)
    (instanceValue : Object.Instance Key Values (plan changed)) :
    changedRelation.holds instanceValue.state := by
  change instanceValue.state .derived =
    (instanceValue.state .source).map (· + 1)
  rw [← instanceValue.agrees .derived]
  rfl

private theorem stableRelationHolds (changed : Nat)
    (instanceValue : Object.Instance Key Values (plan changed)) :
    stableRelation.holds instanceValue.state := by
  change instanceValue.state .stableDerived =
    (instanceValue.state .stableSource).map (· * 2)
  rw [← instanceValue.agrees .stableDerived]
  rfl

private def certified (current : Object.Instance Key Values (plan 20)) :
    Proof.CertifiedObject Key Values (plan 20) :=
  { instanceValue := current
    obligations := [changedRelation, stableRelation]
    certificate := by
      intro obligation membership
      have owned : obligation = changedRelation ∨
          obligation = stableRelation := by
        simpa [Proof.proofObjectOfInstance] using membership
      rcases owned with changed | stable
      · subst obligation
        exact changedRelationHolds 20 current
      · subst obligation
        exact stableRelationHolds 20 current }

private def certifiedRevision
    (current : Object.Instance Key Values (plan 20))
    (revision : Object.Revision (dependencies 30) [.source]
      [.source, .derived, .stableSource, .stableDerived]) :
    Proof.CertifiedObject Key Values (plan 30) :=
  (certified current).applyRevision revision (sameResolver current) [] (by
    intro obligation membership
    have selected := (Proof.mem_pending_iff
      (Proof.proofObjectOfInstance current
        [changedRelation, stableRelation])
      (Proof.patchOfRevision revision) obligation).mp membership
    rcases selected with ⟨owned, _⟩ | fresh
    · have choice : obligation = changedRelation ∨
          obligation = stableRelation := by
        simpa [Proof.proofObjectOfInstance] using owned
      rcases choice with changed | stable
      · subst obligation
        exact changedRelationHolds 30 revision.instanceValue
      · subst obligation
        exact stableRelationHolds 30 revision.instanceValue
    · simp [Proof.patchOfRevision] at fresh)

example (current : Object.Instance Key Values (plan 20))
    (revision : Object.Revision (dependencies 30) [.source]
      [.source, .derived, .stableSource, .stableDerived]) :
    stableRelation.holds
      (certifiedRevision current revision).instanceValue.state :=
  (certifiedRevision current revision).certificate stableRelation (by
    change stableRelation ∈
      [changedRelation, stableRelation] ++ []
    simp)

private structure Outcome where
  invalidated : List Key
  retained : List Key
  stableValue : Option (Option Nat)
  recomputedValue : Option Nat
  repairs : List Bool
  deriving DecidableEq, Repr

private def observed : Option Outcome := do
  let oldScheduled ← ((dependencies 20).scheduleRanked).toOption
  let current := oldScheduled.ranked.instantiate
  let keys := [.source, .derived, .stableSource, .stableDerived]
  let oldCache := (current.cache keys).force keys
  let revision ← ((dependencies 30).revise [.source] current keys oldCache
    (sameResolver current)).toOption
  let certifiedNext := certifiedRevision current revision
  let impact := revision.impact
  let reused := revision.cache
  let proofImpact := Proof.Debug.explainPatch
    (Proof.proofObjectOfInstance current
      [changedRelation, stableRelation])
    (Proof.patchOfRevision revision)
  return {
    invalidated := keys.filter impact.affected
    retained := keys.filter fun key => (reused.peek key).isSome
    stableValue := reused.peek .stableDerived
    recomputedValue := certifiedNext.instanceValue.state .derived
    repairs := proofImpact.map Proof.Debug.Impact.needsRepair
  }

example : observed = some {
    invalidated := [.source, .derived]
    retained := [.stableSource, .stableDerived]
    stableValue := some (some 14)
    recomputedValue := some 31
    repairs := [true, false]
  } := by
  native_decide

example (oldScheduled : Object.Scheduled (dependencies 20))
    (newScheduled : Object.Scheduled (dependencies 30))
    (impact : Object.Impact (dependencies 30) [.source])
    (unaffected : impact.affected .stableDerived = false) :
    let current := oldScheduled.ranked.instantiate
    let next := newScheduled.ranked.instantiate
    current.state .stableDerived = next.state .stableDerived := by
  exact newScheduled.stableState [.source] impact
    oldScheduled.ranked.instantiate newScheduled.ranked.instantiate
    (sameResolver _) .stableDerived unaffected

private def diagnostic : Option (List (Object.Debug.ImpactRow Key)) := do
  let oldScheduled ← ((dependencies 20).scheduleRanked).toOption
  let current := oldScheduled.ranked.instantiate
  let keys := [.source, .derived, .stableSource, .stableDerived]
  let oldCache := (current.cache keys).force keys
  let revision ← ((dependencies 30).revise [.source] current keys oldCache
    (sameResolver current)).toOption
  some (Object.Debug.Revision.explainImpact revision)

#eval (do
  if (← IO.getEnv "LEANPOO_VERBOSE") == some "1" then
    IO.println (repr diagnostic) : IO Unit)

end IncrementalObjectExample
