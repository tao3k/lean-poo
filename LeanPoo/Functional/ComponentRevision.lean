import LeanPoo.Functional.SupportRevision

/-! Ordered service contributions share one final support revision. This is a
finite generalized-protocol future-work extension, not unrestricted mutation. -/
namespace LeanPoo.Functional.GeneralizedGraph
variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

/-- One service's membership and dependent provider edits, before joint validation. -/
structure RevisionFragment (Key : Type) (Value : Key → Type) where
  added : List Key
  removed : List Key
  codes : List ((key : Key) × Option (Code Key Value key))
  bases : List ((key : Key) × Option (Outcome Key Value key))

/-- Final support retains old order, then appends contributions in submitted order. -/
def RevisionFragment.keys (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) : List Key :=
  spec.keys.filter (fun key => decide (key ∉ parts.flatMap RevisionFragment.removed)) ++
    parts.flatMap RevisionFragment.added

/-- Additions must be fresh, removals current, and neither may be repeated. This
also excludes ambiguous delete/re-add of a single key within one publication. -/
def RevisionFragment.Valid (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) : Prop :=
  (parts.flatMap RevisionFragment.added).Nodup ∧
  (parts.flatMap RevisionFragment.removed).Nodup ∧
  (∀ key ∈ parts.flatMap RevisionFragment.added, key ∉ spec.keys) ∧
  (∀ key ∈ parts.flatMap RevisionFragment.removed, key ∈ spec.keys)

/-- Collect all service contributions before ordinary typed provider validation.
Dependencies may cross contributions; checked SCC discovery validates the final
source later, before any builder or current admission can run. -/
def SupportRevision.join (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) :
    Except String (SupportRevision spec) :=
  letI : Decidable (RevisionFragment.Valid spec parts) := by unfold RevisionFragment.Valid; infer_instance
  if RevisionFragment.Valid spec parts then
    SupportRevision.create spec (RevisionFragment.keys spec parts)
      (parts.flatMap RevisionFragment.codes) (parts.flatMap RevisionFragment.bases)
  else .error "conflicting or stale component membership contributions"

/-- Anchor staged edits to an abstract publication identity. Native uses the
exact live graph-cache object; identities are not inferred from support or values. -/
def SupportRevision.joinAt {Snapshot : Type} [DecidableEq Snapshot] (expected current : Snapshot)
    (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) :
    Except String (SupportRevision spec) :=
  if current = expected then join spec parts else .error "stale component revision snapshot"

/-- A staged action cannot run on another publication, including an equal-valued
round trip. This does not assume that support differences detect all revisions. -/
theorem SupportRevision.joinAt_stale {Snapshot : Type} [DecidableEq Snapshot] (expected current : Snapshot)
    (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) (stale : current ≠ expected) :
    joinAt expected current spec parts = .error "stale component revision snapshot" := by
  simp [joinAt, stale]

/-- On the exact expected publication, all existing joint-revision laws apply. -/
theorem SupportRevision.joinAt_current {Snapshot : Type} [DecidableEq Snapshot] (current : Snapshot)
    (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) :
    joinAt current current spec parts = join spec parts := by simp [joinAt]

/-- Any successful anchored batch has the requested publication identity and
ordinary checked joint edits. Snapshot freshness remains an implementation premise. -/
theorem SupportRevision.joinAt_accepted {Snapshot : Type} [DecidableEq Snapshot] (expected current : Snapshot)
    (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value)) (revision : SupportRevision spec)
    (accepted : joinAt expected current spec parts = .ok revision) :
    current = expected ∧ join spec parts = .ok revision := by
  unfold joinAt at accepted
  split at accepted
  · exact ⟨by assumption,accepted⟩
  · contradiction

/-- Joint acceptance certifies membership edits against the SAME old snapshot. -/
theorem SupportRevision.join_valid (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision) :
    RevisionFragment.Valid spec parts := by
  unfold join at accepted
  split at accepted
  · assumption
  · contradiction

/-- All exact submitted dependent edits and final keys belong to one accepted
revision. No contribution is overwritten by a later service's conflicting write. -/
theorem SupportRevision.join_fields (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision) :
    revision.keys = RevisionFragment.keys spec parts ∧
    revision.edits.codes = parts.flatMap RevisionFragment.codes ∧
    revision.edits.bases = parts.flatMap RevisionFragment.bases := by
  unfold join at accepted
  split at accepted
  · unfold create at accepted
    split at accepted
    · cases found : Revision.create (spec.restrict (RevisionFragment.keys spec parts))
          (parts.flatMap RevisionFragment.codes) (parts.flatMap RevisionFragment.bases) with
      | error message => simp [found] at accepted
      | ok edits =>
        have fields := Revision.create_fields _ _ _ edits found
        simp only [found] at accepted
        cases accepted
        exact ⟨rfl,fields⟩
    · contradiction
  · contradiction

/-- Current support is exactly the surviving old components plus fresh additions. -/
theorem SupportRevision.join_members (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision) (key : Key) :
    key ∈ revision.apply.keys ↔
      (key ∈ spec.keys ∧ key ∉ parts.flatMap RevisionFragment.removed) ∨
      key ∈ parts.flatMap RevisionFragment.added := by
  rw [apply_keys, (join_fields spec parts revision accepted).1]
  simp [RevisionFragment.keys]

/-- Duplicate code OR base contributions cannot pass joint validation, even when
both services supply extensionally equal payloads. No last-writer policy is hidden. -/
theorem SupportRevision.join_unique (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision) :
    ((parts.flatMap RevisionFragment.codes).map Sigma.fst).Nodup ∧
    ((parts.flatMap RevisionFragment.bases).map Sigma.fst).Nodup := by
  have fields := join_fields spec parts revision accepted
  rw [← fields.2.1, ← fields.2.2]
  exact ⟨revision.edits.uniqueCodes,revision.edits.uniqueBases⟩

/-- Every jointly removed key loses both providers, even if other services add
components during that same publication. The old source is not mutated. -/
theorem SupportRevision.join_erased (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision)
    (key : Key) (removed : key ∈ parts.flatMap RevisionFragment.removed) :
    revision.apply.code key = none ∧ revision.apply.base key = none := by
  apply revision.erased key
  intro active
  have member := (join_members spec parts revision accepted key).mp active
  rcases member with survivor | fresh
  · exact survivor.2 removed
  · have valid := join_valid spec parts revision accepted
    exact valid.2.2.1 key fresh (valid.2.2.2 key removed)
/-- Jointly added components inherit only explicit writes, even when the same key
had latent providers outside the old support. Other services cannot resurrect them. -/
theorem SupportRevision.join_fresh (spec : Declaration Key Value) (parts : List (RevisionFragment Key Value))
    (revision : SupportRevision spec) (accepted : SupportRevision.join spec parts = .ok revision)
    (key : Key) (added : key ∈ parts.flatMap RevisionFragment.added) :
    revision.apply.code key = (selectEdit revision.edits.codes key).getD none ∧
    revision.apply.base key = (selectEdit revision.edits.bases key).getD none := by
  exact revision.fresh_defaults key ((join_valid spec parts revision accepted).2.2.1 key added)
end LeanPoo.Functional.GeneralizedGraph
