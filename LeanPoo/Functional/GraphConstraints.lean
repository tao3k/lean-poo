import LeanPoo.Functional.GraphMigration
import LeanPoo.Functional.Absence
import LeanPoo.Functional.ContextSlot

/-! Join positive/negative capabilities and context caches at the actual next
graph snapshot. Fresh factories require fresh joint proof admission. -/
namespace LeanPoo.Functional.Requirements

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {provider : Provider Context Key Value} {keys positiveKeys negativeKeys : List Key}
variable {Claim : ∀ c, Results Value c keys → Prop}
variable {positiveClaim : ∀ c, Results Value c positiveKeys → Prop}

def BuiltContextCache (cache : CachedPreparation provider keys Claim) : Type (max u w) :=
  match cache.outcome with
  | .error _ => PUnit
  | .ok ready => ContextSlot ready

def BuiltContextCache.empty (cache : CachedPreparation provider keys Claim) : BuiltContextCache cache :=
  match outcome : cache.outcome with
  | .error _ => by simpa only [BuiltContextCache, outcome] using PUnit.unit
  | .ok ready => by simpa only [BuiltContextCache, outcome] using ContextSlot.empty ready

structure ConstraintCache (provider : Provider Context Key Value)
    (positiveKeys negativeKeys : List Key) (Claim : ∀ c, Results Value c positiveKeys → Prop) where
  positive : CachedPreparation provider positiveKeys Claim
  contexts : BuiltContextCache positive
  negative : AbsenceCertificate provider negativeKeys

structure ConstraintRead (cache : ConstraintCache provider positiveKeys negativeKeys positiveClaim) (context : Context) where
  data : Results Value context positiveKeys
  correct : positiveClaim context data
  aligned : ∀ ready, cache.positive.outcome = .ok ready → data = build ready.factories context
  next : ConstraintCache provider positiveKeys negativeKeys positiveClaim
  continued : next.positive = cache.positive
  reused : Bool

/-- Use the same ContextSlot on a retained certified family. Changing context
builds fresh data; changing a graph may retain this slot only through proved
selection equality. Missing positive capabilities retain their exact error. -/
def ConstraintCache.read [DecidableEq Context]
    (cache : ConstraintCache provider positiveKeys negativeKeys positiveClaim) (context : Context) :
    Except Key (ConstraintRead cache context) :=
  match outcome : cache.positive.outcome with
  | .error key => .error key
  | .ok ready =>
    let slot : ContextSlot ready := by simpa only [BuiltContextCache, outcome] using cache.contexts
    let (data, next, reused) := slot.read context
    .ok {
      data := data.val, correct := data.property.2
      aligned := by
        intro other found
        have same : ready = other := Except.ok.inj (outcome.symm.trans found)
        subst other
        exact data.property.1
      next := {cache with contexts := by simpa only [BuiltContextCache, outcome] using next}
      continued := rfl
      reused }

inductive PositiveGraphRevision (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop) where
  | reused (cache : CachedPreparation provider keys Claim) (contexts : BuiltContextCache cache)
      (available : ∃ ready, cache.outcome = .ok ready)
  | fresh (prepared : Prepared provider keys) (available : ∃ factories, prepared.outcome = .ok factories)

def PositiveGraphRevision.forget (revision : PositiveGraphRevision provider keys Claim) :
    Except Key (Factories Context Value keys) := match revision with
  | .reused cache _ _ => cache.outcome.map Certified.factories
  | .fresh prepared _ => prepared.outcome

def PositiveGraphRevision.isReused (revision : PositiveGraphRevision provider keys Claim) : Bool :=
  match revision with | .reused .. => true | .fresh .. => false

theorem PositiveGraphRevision.aligned (revision : PositiveGraphRevision provider keys Claim) :
    revision.forget = prepare provider keys := by
  cases revision with
  | reused cache contexts available => exact cache.aligned
  | fresh prepared available => exact prepared.aligned

theorem PositiveGraphRevision.available (revision : PositiveGraphRevision provider keys Claim) :
    ∃ factories, prepare provider keys = .ok factories := by
  cases revision with
  | reused cache contexts available =>
    obtain ⟨ready, outcome⟩ := available
    refine ⟨ready.factories, ?_⟩
    simpa [outcome, Except.map] using cache.aligned.symm
  | fresh prepared available =>
    obtain ⟨factories, outcome⟩ := available
    exact ⟨factories, prepared.aligned.symm.trans outcome⟩

/-- Only fresh selections incur a new analytic admission obligation. -/
def PositiveGraphRevision.Admission (revision : PositiveGraphRevision provider keys Claim) : Prop :=
  match revision with
  | .reused _ _ _ => True
  | .fresh _ _ => ∀ f, Selected provider keys f → ∀ c, Claim c (build f c)

/-- Reused retains the joint proof and built context slot. Fresh certifies the
already prepared tuple and starts an empty slot, without another selection pass. -/
def PositiveGraphRevision.certify (revision : PositiveGraphRevision provider keys Claim)
    (admit : revision.Admission) :
    (cache : CachedPreparation provider keys Claim) × BuiltContextCache cache :=
  match revision, admit with
  | .reused cache contexts _, _ => ⟨cache, contexts⟩
  | .fresh prepared _, admit =>
    let cache := prepared.certify Claim admit
    ⟨cache, BuiltContextCache.empty cache⟩

theorem PositiveGraphRevision.certify_forget (revision : PositiveGraphRevision provider keys Claim)
    (admit : revision.Admission) :
    (revision.certify admit).1.outcome.map Certified.factories = revision.forget := by
  cases revision with
  | reused cache contexts available => rfl
  | fresh prepared available => exact prepared.certify_forget Claim admit

/-- A stable migration retains the exact slot and certified outcome, including
already built data and arbitrary joint proof evidence. -/
@[simp] theorem PositiveGraphRevision.certify_reused (cache : CachedPreparation provider keys Claim)
    (contexts : BuiltContextCache cache) (available : ∃ ready, cache.outcome = .ok ready) :
    (PositiveGraphRevision.reused cache contexts available).certify True.intro = ⟨cache, contexts⟩ := rfl

variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]
variable {oldRegistry : IndexedRegistry Context Key Value} {graph : C4.Graph} {root : String}
variable {newProviders : String → Provider Context Key Value} {edits : List (RegistryEdit Context Key Value)}

structure GraphConstraintRevision (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (positiveKeys negativeKeys : List Key) (Claim : ∀ c, Results Value c positiveKeys → Prop) where
  negative : AbsenceCertificate (assemble target.index.order target.registry.dictionary) negativeKeys
  positive : PositiveGraphRevision (assemble target.index.order target.registry.dictionary) positiveKeys Claim

inductive GraphConstraintFailure (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (positiveKeys negativeKeys : List Key) where
  | introduced (conflict : Presence (assemble target.index.order target.registry.dictionary) negativeKeys)
  | missing (key : Key) (failed : prepare (assemble target.index.order target.registry.dictionary) positiveKeys = .error key)

/-- Check all watched absences before preparing required capabilities. Stable
winning identities and disjoint edit scope automatically rebind the old positive
cache and its context slot; otherwise retain fresh factories awaiting admission. -/
def reviseGraphConstraints (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : ConstraintCache (assemble oldIndex.order oldRegistry.dictionary) positiveKeys negativeKeys positiveClaim)
    (scope : KeyIndex positiveKeys) (target : PreparedGraphMigration oldRegistry graph root newProviders edits) :
    Except (GraphConstraintFailure target positiveKeys negativeKeys)
      (GraphConstraintRevision target positiveKeys negativeKeys positiveClaim) :=
  match checkAbsent (assemble target.index.order target.registry.dictionary) negativeKeys with
  | .error conflict => .error (.introduced conflict)
  | .ok negative =>
    if retained : target.canReuse oldIndex.order scope = true then
      let positive := cache.positive.rebind _ (target.reuse_preparation oldIndex.order scope retained)
      match outcome : positive.outcome with
      | .error key => .error (.missing key (by simpa [outcome, Except.map] using positive.aligned.symm))
      | .ok ready => .ok ⟨negative, .reused positive cache.contexts ⟨ready, outcome⟩⟩
    else
      let prepared : Prepared (assemble target.index.order target.registry.dictionary) positiveKeys :=
        ⟨prepare (assemble target.index.order target.registry.dictionary) positiveKeys, rfl⟩
      match outcome : prepared.outcome with
      | .error key => .error (.missing key outcome)
      | .ok factories => .ok ⟨negative, .fresh prepared ⟨factories, outcome⟩⟩

/-- Complete capability admission on the actual compiled/patched target.
Analytic joint admission is a separate obligation for fresh factories. -/
theorem reviseGraphConstraints_ok_iff (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : ConstraintCache (assemble oldIndex.order oldRegistry.dictionary) positiveKeys negativeKeys positiveClaim)
    (scope : KeyIndex positiveKeys) (target : PreparedGraphMigration oldRegistry graph root newProviders edits) :
    (∃ revision, reviseGraphConstraints oldIndex cache scope target = .ok revision) ↔
      Absent (assemble target.index.order target.registry.dictionary) negativeKeys ∧
      ∃ factories, prepare (assemble target.index.order target.registry.dictionary) positiveKeys = .ok factories := by
  constructor
  · rintro ⟨revision, _⟩
    exact ⟨revision.negative.absent, revision.positive.available⟩
  · rintro ⟨absent, factories, available⟩
    cases outcome : reviseGraphConstraints oldIndex cache scope target with
    | ok revision => exact ⟨revision, rfl⟩
    | error failure =>
      cases failure with
      | introduced conflict => exact False.elim (conflict.refutes absent)
      | missing key failed => rw [available] at failed; contradiction

/-- Publish a new certified cache only after admitting fresh joint constraints.
Every part is indexed by the target registry/order; stable context data survives. -/
def GraphConstraintRevision.certify
    (revision : GraphConstraintRevision target positiveKeys negativeKeys positiveClaim)
    (admit : revision.positive.Admission) :
    ConstraintCache (assemble target.index.order target.registry.dictionary) positiveKeys negativeKeys positiveClaim :=
  let saved := revision.positive.certify admit
  ⟨saved.1, saved.2, revision.negative⟩

omit [DecidableEq Key] in
/-- Accepted and analytically admitted revisions always have a complete
certified family; a published read cannot expose a missing positive key. -/
theorem GraphConstraintRevision.certify_available
    (revision : GraphConstraintRevision target positiveKeys negativeKeys positiveClaim)
    (admit : revision.positive.Admission) :
    ∃ ready, (revision.certify admit).positive.outcome = .ok ready := by
  obtain ⟨factories, prepared⟩ := revision.positive.available
  have projected := revision.positive.certify_forget admit
  rw [revision.positive.aligned, prepared] at projected
  change (revision.certify admit).positive.outcome.map Certified.factories = .ok factories at projected
  cases outcome : (revision.certify admit).positive.outcome with
  | error key => simp [outcome, Except.map] at projected
  | ok ready => exact ⟨ready, rfl⟩

def migrateGraphConstraints (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : ConstraintCache (assemble oldIndex.order oldRegistry.dictionary) positiveKeys negativeKeys positiveClaim)
    (scope : KeyIndex positiveKeys) (graph : C4.Graph) (root : String)
    (newProviders : String → Provider Context Key Value) (edits : List (RegistryEdit Context Key Value)) :
    Except GraphMigrationError ((target : PreparedGraphMigration oldRegistry graph root newProviders edits) ×
      Except (GraphConstraintFailure target positiveKeys negativeKeys)
        (GraphConstraintRevision target positiveKeys negativeKeys positiveClaim)) :=
  (prepareGraphMigration oldRegistry graph root newProviders edits).map fun target =>
    ⟨target, reviseGraphConstraints oldIndex cache scope target⟩

end LeanPoo.Functional.Requirements
