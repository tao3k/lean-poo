import LeanPoo.Functional.AnalyzedCache
import LeanPoo.Functional.GraphConstraints

/-! Inferred dependencies extend capability contracts and govern computed-result
cache reuse on the actual compiled/patched graph. Unknown footprints require new
result admission; presence-only observations do not compare function bodies. -/
namespace LeanPoo.Functional
open Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Result : Context → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]
variable {oldRegistry : IndexedRegistry Context Key Value} {graph : C4.Graph} {root : String}
variable {newProviders : String → Provider Context Key Value} {edits : List (RegistryEdit Context Key Value)}

/-- Preserve data reads by exact selection; compare availability directly on
completed snapshots. Unknown callbacks never qualify for automatic reuse. -/
def PreparedGraphMigration.canReuseComputation
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (oldOrder : C4.VerifiedOrder oldGraph oldRoot)
    (code : Computation Context Key Value Result) (scope : KeyIndex code.analyze.values) : Bool :=
  !code.analyze.unknown && target.canReuse oldOrder scope &&
    code.analyze.presences.all (fun key =>
      (assemble target.index.order target.registry.dictionary key).isSome ==
        (assemble oldOrder oldRegistry.dictionary key).isSome)

omit [DecidableEq Key] in
/-- Provider-wide callbacks require fresh computed-result admission on every
revision, even if all explicitly listed capabilities remain unchanged. -/
theorem PreparedGraphMigration.unknown_computation
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (oldOrder : C4.VerifiedOrder oldGraph oldRoot)
    (code : Computation Context Key Value Result) (scope : KeyIndex code.analyze.values)
    (unknown : code.analyze.unknown = true) : target.canReuseComputation oldOrder code scope = false := by
  simp [canReuseComputation, unknown]

/-- The inferred reuse decision proves universal equality of actual execution,
including values and source/capability errors, without evaluating any factory. -/
theorem PreparedGraphMigration.reuse_computation
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (oldOrder : C4.VerifiedOrder oldGraph oldRoot)
    (code : Computation Context Key Value Result) (scope : KeyIndex code.analyze.values)
    (retained : target.canReuseComputation oldOrder code scope = true) (context : Context) :
    code.evaluate (assemble target.index.order target.registry.dictionary) context =
      code.evaluate (assemble oldOrder oldRegistry.dictionary) context := by
  have conditions : code.analyze.unknown = false ∧ target.canReuse oldOrder scope = true ∧
      code.analyze.presences.all (fun key =>
        (assemble target.index.order target.registry.dictionary key).isSome ==
          (assemble oldOrder oldRegistry.dictionary key).isSome) = true := by
    simpa [canReuseComputation, Bool.and_eq_true, and_assoc] using retained
  apply code.evaluate_congr _ _ conditions.1
  · exact target.reuse_selection oldOrder scope conditions.2.1
  · intro key member
    exact beq_iff_eq.mp (List.all_eq_true.mp conditions.2.2 key member)

/-- Positive and negative lists are expanded from syntax, not caller dependency
annotations. The joint Claim covers the complete expanded positive tuple. -/
structure AnalyzedConstraintCache (code : Computation Context Key Value Result)
    (provider : Provider Context Key Value) (positive negative : List Key)
    (Joint : ∀ c, Results Value c (positive ++ code.analyze.required) → Prop)
    (Claim : ∀ c, Result c → Prop) where
  capabilities : ConstraintCache provider (positive ++ code.analyze.required) (negative ++ code.analyze.forbidden) Joint
  computed : Computation.Cache code provider Claim
  positiveScope : KeyIndex (positive ++ code.analyze.required)
  dependencyScope : KeyIndex code.analyze.values

variable {code : Computation Context Key Value Result} {provider : Provider Context Key Value}
variable {positive negative : List Key}
variable {Joint : ∀ c, Results Value c (positive ++ code.analyze.required) → Prop}
variable {Claim : ∀ c, Result c → Prop}

/-- Retain the inferred key indices once. Existing capability admission supplies
the raw family; the computation's own result contract is admitted separately. -/
def AnalyzedConstraintCache.start
    (capabilities : ConstraintCache provider (positive ++ code.analyze.required) (negative ++ code.analyze.forbidden) Joint)
    (admit : ∀ c, Computation.OutcomeValid Claim c (code.evaluate provider c)) :
    AnalyzedConstraintCache code provider positive negative Joint Claim :=
  ⟨capabilities, Computation.Cache.empty code provider Claim admit,
    KeyIndex.ofKeys _, KeyIndex.ofKeys _⟩

omit [LawfulBEq Key] [DecidableEq Key] in
def AnalyzedConstraintCache.read [DecidableEq Context]
    (cache : AnalyzedConstraintCache code provider positive negative Joint Claim) (context : Context) :
    {outcome : Except (ComputationError Key) (Result context) //
      outcome = code.evaluate provider context ∧ Computation.OutcomeValid Claim context outcome} ×
      AnalyzedConstraintCache code provider positive negative Joint Claim × Bool :=
  let (outcome, next, reused) := cache.computed.read context
  (outcome, {cache with computed := next}, reused)

inductive ComputedRevision (code : Computation Context Key Value Result) (provider : Provider Context Key Value)
    (Claim : ∀ c, Result c → Prop) where
  | reused (cache : Computation.Cache code provider Claim)
  | fresh

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] in
def ComputedRevision.isReused (revision : ComputedRevision code provider Claim) : Bool :=
  match revision with | .reused _ => true | .fresh => false

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] in
def ComputedRevision.Admission (revision : ComputedRevision code provider Claim) : Prop :=
  match revision with
  | .reused _ => True
  | .fresh => ∀ c, Computation.OutcomeValid Claim c (code.evaluate provider c)

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] in
def ComputedRevision.certify (revision : ComputedRevision code provider Claim)
    (admit : revision.Admission) : Computation.Cache code provider Claim :=
  match revision, admit with
  | .reused cache, _ => cache
  | .fresh, admit => Computation.Cache.empty code provider Claim admit

structure AnalyzedConstraintRevision
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits)
    (code : Computation Context Key Value Result) (positive negative : List Key)
    (Joint : ∀ c, Results Value c (positive ++ code.analyze.required) → Prop) (Claim : ∀ c, Result c → Prop) where
  capabilities : GraphConstraintRevision target (positive ++ code.analyze.required) (negative ++ code.analyze.forbidden) Joint
  computed : ComputedRevision code (assemble target.index.order target.registry.dictionary) Claim
  positiveScope : KeyIndex (positive ++ code.analyze.required)
  dependencyScope : KeyIndex code.analyze.values

/-- Capability conflicts refuse before any computed body runs. Stable inferred
observations preserve the result proof and hot slot; affected/unknown computations
retain no old slot and require new result admission. -/
def reviseAnalyzedConstraints (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : AnalyzedConstraintCache code (assemble oldIndex.order oldRegistry.dictionary) positive negative Joint Claim)
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits) :
    Except (GraphConstraintFailure target (positive ++ code.analyze.required) (negative ++ code.analyze.forbidden))
      (AnalyzedConstraintRevision target code positive negative Joint Claim) :=
  match reviseGraphConstraints oldIndex cache.capabilities cache.positiveScope target with
  | .error failure => .error failure
  | .ok capabilities =>
    if retained : target.canReuseComputation oldIndex.order code cache.dependencyScope = true then
      .ok ⟨capabilities, .reused (cache.computed.rebind _
        (fun c => (target.reuse_computation oldIndex.order code cache.dependencyScope retained c).symm)),
        cache.positiveScope, cache.dependencyScope⟩
    else .ok ⟨capabilities, .fresh, cache.positiveScope, cache.dependencyScope⟩

/-- The actual publication branch agrees with the computed dependency decision;
capability errors are preserved before that decision can publish a cache. -/
theorem reviseAnalyzedConstraints_reuse (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : AnalyzedConstraintCache code (assemble oldIndex.order oldRegistry.dictionary) positive negative Joint Claim)
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits) :
    (reviseAnalyzedConstraints oldIndex cache target).map (fun revision => revision.computed.isReused) =
      (reviseGraphConstraints oldIndex cache.capabilities cache.positiveScope target).map
        (fun _ => target.canReuseComputation oldIndex.order code cache.dependencyScope) := by
  unfold reviseAnalyzedConstraints
  cases outcome : reviseGraphConstraints oldIndex cache.capabilities cache.positiveScope target with
  | error failure => rfl
  | ok capabilities =>
    by_cases retained : target.canReuseComputation oldIndex.order code cache.dependencyScope = true
    · simp [retained, Except.map, ComputedRevision.isReused]
    · have no : target.canReuseComputation oldIndex.order code cache.dependencyScope = false := by
        cases result : target.canReuseComputation oldIndex.order code cache.dependencyScope <;> simp_all
      simp [no, Except.map, ComputedRevision.isReused]

/-- Complete admission for the explicit plus inferred static capability policy.
Both conditional branches contribute conservative requirements and absences. -/
theorem reviseAnalyzedConstraints_ok_iff (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : AnalyzedConstraintCache code (assemble oldIndex.order oldRegistry.dictionary) positive negative Joint Claim)
    (target : PreparedGraphMigration oldRegistry graph root newProviders edits) :
    (∃ revision, reviseAnalyzedConstraints oldIndex cache target = .ok revision) ↔
      Absent (assemble target.index.order target.registry.dictionary) (negative ++ code.analyze.forbidden) ∧
      ∃ f, prepare (assemble target.index.order target.registry.dictionary) (positive ++ code.analyze.required) = .ok f := by
  constructor
  · rintro ⟨revision, _⟩
    exact ⟨revision.capabilities.negative.absent, revision.capabilities.positive.available⟩
  · rintro ⟨absent, f, available⟩
    cases outcome : reviseAnalyzedConstraints oldIndex cache target with
    | ok revision => exact ⟨revision, rfl⟩
    | error failure =>
      cases failure with
      | introduced conflict => exact False.elim (conflict.refutes absent)
      | missing key failed => rw [available] at failed; contradiction

omit [DecidableEq Key] in
/-- Accepted expanded contracts establish every inferred guard on the actual
provider; callers do not need another dependency declaration. -/
theorem AnalyzedConstraintRevision.inferred_guards
    (revision : AnalyzedConstraintRevision target code positive negative Joint Claim) :
    (∀ key ∈ code.analyze.required, (assemble target.index.order target.registry.dictionary key).isSome = true) ∧
    (∀ key ∈ code.analyze.forbidden, assemble target.index.order target.registry.dictionary key = none) := by
  constructor
  · intro key member
    obtain ⟨f, prepared⟩ := revision.capabilities.positive.available
    obtain ⟨factory, selected⟩ := Selected.available _ _ f ((prepare_ok_iff _ _ f).mp prepared) key
      (List.mem_append.mpr (Or.inr member))
    simp [selected]
  · intro key member
    exact revision.capabilities.negative.absent key (List.mem_append.mpr (Or.inr member))

omit [DecidableEq Key] in
/-- Known admitted computations cannot expose a capability error after target
publication. Explicit source errors retain their ordinary semantics. -/
theorem AnalyzedConstraintRevision.evaluate_safe
    (revision : AnalyzedConstraintRevision target code positive negative Joint Claim)
    (known : code.analyze.unknown = false) (context : Context) :
    CapabilitySafe (code.evaluate (assemble target.index.order target.registry.dictionary) context) :=
  code.evaluate_capabilitySafe _ known revision.inferred_guards.1 revision.inferred_guards.2 context

def AnalyzedConstraintRevision.certify
    (revision : AnalyzedConstraintRevision target code positive negative Joint Claim)
    (joint : revision.capabilities.positive.Admission) (result : revision.computed.Admission) :
    AnalyzedConstraintCache code (assemble target.index.order target.registry.dictionary) positive negative Joint Claim :=
  ⟨revision.capabilities.certify joint, revision.computed.certify result,
    revision.positiveScope, revision.dependencyScope⟩

/-- Compile and complete the provider transaction before using either inferred
or explicit assumptions. Refused candidates remain diagnostic snapshots. -/
def migrateAnalyzedConstraints (oldIndex : C4.AncestryIndex oldGraph oldRoot)
    (cache : AnalyzedConstraintCache code (assemble oldIndex.order oldRegistry.dictionary) positive negative Joint Claim)
    (graph : C4.Graph) (root : String) (newProviders : String → Provider Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) :
    Except GraphMigrationError ((target : PreparedGraphMigration oldRegistry graph root newProviders edits) ×
      Except (GraphConstraintFailure target (positive ++ code.analyze.required) (negative ++ code.analyze.forbidden))
        (AnalyzedConstraintRevision target code positive negative Joint Claim)) :=
  (prepareGraphMigration oldRegistry graph root newProviders edits).map fun target =>
    ⟨target, reviseAnalyzedConstraints oldIndex cache target⟩

end LeanPoo.Functional
