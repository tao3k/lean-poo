import LeanPoo.Functional.BuildCache

/-! Build identity, disjoint group assembly and a bounded cost illustration. -/
namespace LeanPoo.Examples.ConstructionWorkflow
open LeanPoo.Functional.ConstructionCache
/-- The release and shared source keys stay explicit; no runtime is imported. -/
def buildLibrary : LibraryIdentity := ⟨"release/compiler/linker", "shared-source", "exact-compiled-bytes"⟩
/-- An unchanged compiled group may be restamped for a current run. -/
example : buildAdmitted ⟨buildLibrary, "tests-v2", "objects"⟩ 8
    ⟨⟨buildLibrary, "tests-v2", "objects"⟩, 3, 8⟩ := buildAdmitted_reuse _ _ _
/-- A stale test snapshot refuses even if stamped with the current revision. -/
example : ¬ buildAdmitted ⟨buildLibrary, "tests-v2", "objects"⟩ 8
    ⟨⟨buildLibrary, "tests-v1", "objects"⟩, 3, 8⟩ := by
  simp [buildAdmitted]
/-- Shared prerequisites plus the largest group, before actual queue overhead. -/
example : parallelBuildCost 100 [30, 10, 20] = 130 := rfl
/-- The same work performed serially still includes all three groups. -/
example : 100 + ([30, 10, 20] : List Nat).sum = 160 := rfl
#print axioms buildAdmitted_snapshot
#print axioms buildCoverage_complete
#print axioms parallelBuildCost_le_serial
end LeanPoo.Examples.ConstructionWorkflow
