import LeanPoo.Functional.GraphRevision

/-! A final finite support and its dependent code/base edits are staged together.
Removed and newly admitted keys never inherit unsupported latent definitions. -/
namespace LeanPoo.Functional.GeneralizedGraph
variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

/-- Retain bindings ONLY in the intersection of old and final support. This is
explicit removal, rather than the legacy support view that keeps latent bindings. -/
def Declaration.restrict (spec : Declaration Key Value) (keys : List Key) : Declaration Key Value :=
  ⟨keys,fun key => if key ∈ keys ∧ key ∈ spec.keys then spec.code key else none,
    fun key => if key ∈ keys ∧ key ∈ spec.keys then spec.base key else none⟩

/-- One admitted support revision reuses ordinary typed batch validation. -/
structure SupportRevision (spec : Declaration Key Value) where
  keys : List Key
  unique : keys.Nodup
  edits : Revision (spec.restrict keys)

/-- Validate final support and edits before any component construction or approval.
Fresh supported slots default to absence; callers provide their actual definitions. -/
def SupportRevision.create (spec : Declaration Key Value) (keys : List Key)
    (codes : List ((key : Key) × Option (Code Key Value key)))
    (bases : List ((key : Key) × Option (Outcome Key Value key))) : Except String (SupportRevision spec) :=
  if valid : keys.Nodup then
    match Revision.create (spec.restrict keys) codes bases with
    | .error message => .error message
    | .ok edits => .ok ⟨keys,valid,edits⟩
  else .error "duplicate final component support"

/-- Successful support admission preserves the exact requested key sequence. -/
theorem SupportRevision.create_keys (spec : Declaration Key Value) (keys : List Key)
    (codes : List ((key : Key) × Option (Code Key Value key)))
    (bases : List ((key : Key) × Option (Outcome Key Value key))) (revision : SupportRevision spec)
    (accepted : SupportRevision.create spec keys codes bases = .ok revision) : revision.keys = keys := by
  unfold create at accepted
  split at accepted
  · cases found : Revision.create (spec.restrict keys) codes bases with
    | error message => simp [found] at accepted
    | ok edits => simp only [found] at accepted; cases accepted; rfl
  · contradiction

/-- Install final support, surviving bindings and edits without intermediate publication. -/
def SupportRevision.apply {spec : Declaration Key Value} (revision : SupportRevision spec) : Declaration Key Value :=
  revision.edits.apply

/-- The published source has exactly the requested finite support. -/
theorem SupportRevision.apply_keys {spec : Declaration Key Value} (revision : SupportRevision spec) :
    revision.apply.keys = revision.keys := rfl

/-- Removing support erases BOTH provider namespaces, including observable base
fallbacks outside support. No stale provider is retained behind the new declaration. -/
theorem SupportRevision.erased {spec : Declaration Key Value} (revision : SupportRevision spec)
    (key : Key) (removed : key ∉ revision.keys) :
    revision.apply.code key = none ∧ revision.apply.base key = none := by
  have noCode : key ∉ revision.edits.codes.map Sigma.fst := fun member => removed (revision.edits.knownCodes key member)
  have noBase : key ∉ revision.edits.bases.map Sigma.fst := fun member => removed (revision.edits.knownBases key member)
  simp [apply, Revision.apply, selectEdit_none _ key noCode, selectEdit_none _ key noBase,
    Declaration.restrict, removed]

/-- Deleted components resolve to actual absence, not an old out-of-support base. -/
theorem SupportRevision.removed_resolve {spec : Declaration Key Value} (revision : SupportRevision spec)
    (key : Key) (removed : key ∉ revision.keys) (self : State Key Value) :
    revision.apply.resolve key self = none := by
  simp [Declaration.resolve, apply_keys, removed, (revision.erased key removed).2]

/-- A newly admitted node starts only from its submitted edits; latent old code
and base can never reappear merely because the key becomes supported. -/
theorem SupportRevision.fresh_defaults {spec : Declaration Key Value} (revision : SupportRevision spec)
    (key : Key) (fresh : key ∉ spec.keys) :
    revision.apply.code key = (selectEdit revision.edits.codes key).getD none ∧
    revision.apply.base key = (selectEdit revision.edits.bases key).getD none := by
  simp [apply, Revision.apply, Declaration.restrict, fresh]

/-- An unedited surviving component keeps its exact resolver, irrespective of how
many other components were added/removed. Invalidation remains a separate condition. -/
theorem SupportRevision.survivor_frame {spec : Declaration Key Value} (revision : SupportRevision spec)
    (key : Key) (before : key ∈ spec.keys) (after : key ∈ revision.keys)
    (noCode : key ∉ revision.edits.codes.map Sigma.fst) (noBase : key ∉ revision.edits.bases.map Sigma.fst)
    (self : State Key Value) : revision.apply.resolve key self = spec.resolve key self := by
  rw [SupportRevision.apply, Revision.apply_resolve_frame _ key noCode noBase]
  simp [Declaration.resolve, Declaration.restrict, before, after]
end LeanPoo.Functional.GeneralizedGraph
