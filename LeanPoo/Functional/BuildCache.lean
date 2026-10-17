import Std

/-! Source-bound split build admission and ideal parallel critical paths.
Keys represent exact source/toolchain identities. SHA-256 collision resistance,
Actions storage, compiler correctness, queue delays and wall time are premises
of the implementation, not consequences of these pure equations. -/
namespace LeanPoo.Functional.ConstructionCache

/-- Shared compilation binds inputs AND the resulting byte generation. Equal
source inputs need not yield interchangeable compiler-generated private symbols. -/
structure LibraryIdentity where
  toolchain : String
  sources : String
  generation : String
  deriving DecidableEq

/-- Tests add the complete test-source snapshot and a unique functional group.
Conservative snapshot invalidation covers possible cross-group macro imports. -/
structure TestIdentity where
  library : LibraryIdentity
  snapshot : String
  group : String
  deriving DecidableEq

/-- Original producer and current admitted revision have separate roles. -/
structure BuildArtifact where
  identity : TestIdentity
  producer : Nat
  checkedRevision : Nat

/-- A complete artifact must match both current source and current run. -/
def buildAdmitted (expected : TestIdentity) (revision : Nat) (artifact : BuildArtifact) : Prop :=
  artifact.identity = expected ∧ artifact.checkedRevision = revision

/-- No stale snapshot can be converted to current evidence by a revision stamp. -/
theorem buildAdmitted_snapshot (expected : TestIdentity) (revision : Nat) (artifact : BuildArtifact)
    (accepted : buildAdmitted expected revision artifact) :
    artifact.identity.snapshot = expected.snapshot := congrArg TestIdentity.snapshot accepted.1

/-- An old run remains refused, even when the source bytes happen to match. -/
theorem buildAdmitted_revision (expected : TestIdentity) (revision : Nat) (artifact : BuildArtifact)
    (stale : artifact.checkedRevision ≠ revision) : ¬ buildAdmitted expected revision artifact :=
  fun accepted => stale accepted.2

/-- Reuse across commits is allowed only after exact source admission and a fresh
run stamp. A producer SHA alone is never the admission predicate. -/
theorem buildAdmitted_reuse (expected : TestIdentity) (producer revision : Nat) :
    buildAdmitted expected revision ⟨expected, producer, revision⟩ := ⟨rfl, rfl⟩

/-- A shared-byte generation mismatch refuses even at the current revision. -/
theorem buildAdmitted_generation (expected : TestIdentity) (revision : Nat) (artifact : BuildArtifact)
    (different : artifact.identity.library.generation ≠ expected.library.generation) :
    ¬ buildAdmitted expected revision artifact := by
  intro accepted
  exact different (congrArg (fun identity => identity.library.generation) accepted.1)

/-- Test edits preserve shared-library identity but invalidate test artifacts. -/
theorem test_revision_separates_library (library : LibraryIdentity) (old new group : String)
    (changed : old ≠ new) :
    (TestIdentity.mk library old group).library = (TestIdentity.mk library new group).library ∧
      (TestIdentity.mk library old group) ≠ (TestIdentity.mk library new group) := by
  constructor
  · rfl
  · intro equal
    exact changed (congrArg TestIdentity.snapshot equal)

/-- Complete, disjoint group compilation owns exactly the original inventory. -/
def buildCoverage (expected : List String) (groups : List (List String)) : Prop :=
  groups.flatten.Perm expected ∧ groups.flatten.Nodup

/-- Assembly cannot silently drop a test module. -/
theorem buildCoverage_complete (expected : List String) (groups : List (List String))
    (covered : buildCoverage expected groups) (file : String) :
    file ∈ groups.flatten ↔ file ∈ expected := covered.1.mem_iff

/-- Assembly cannot accept the same compilation root twice. -/
theorem buildCoverage_unique (expected : List String) (groups : List (List String))
    (covered : buildCoverage expected groups) : groups.flatten.Nodup := covered.2

/-- Independent group costs on unlimited available workers have this ideal
critical path. Actual queue/transfer/process startup costs are excluded. -/
def parallelBuildCost (shared : Nat) (groups : List Nat) : Nat :=
  shared + groups.foldr Nat.max 0

/-- For the SAME supplied task costs, bound the ideal critical path. This does
not equate a split build's aggregate work with a monolithic compiler invocation:
independent processes may reload shared metadata. -/
theorem parallelBuildCost_le_serial (shared : Nat) (groups : List Nat) :
    parallelBuildCost shared groups ≤ shared + groups.sum := by
  unfold parallelBuildCost
  apply Nat.add_le_add_left
  induction groups with
  | nil => exact Nat.le_refl 0
  | cons cost rest ih =>
    simp only [List.foldr_cons, List.sum_cons]
    exact Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_trans ih (Nat.le_add_left _ _)⟩

end LeanPoo.Functional.ConstructionCache
