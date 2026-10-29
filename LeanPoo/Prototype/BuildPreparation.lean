import Std

/-! Standard build-session sharing, inventories and declared resource envelopes.
These are source-count laws, not a compiler, dyld or physical-GC verification. -/
namespace LeanPoo.Prototype.Representation

/-- Declared test-package allocation; standard make still owns every job. -/
structure BuildAllocation where
  packages : Nat
  backends : Nat
  deriving DecidableEq, Repr

/-- One GXC process plus its bounded GSC executor capacity per package. This is
not an OS thread count. The waiting CLI is included in the heap envelope. -/
def BuildAllocation.slots (allocation : BuildAllocation) : Nat :=
  allocation.packages * (allocation.backends + 1)

/-- CLI and GXC each have 1 GiB; each GSC has 2 GiB. This is a declared Scheme
heap envelope, excluding C compiler RSS, mappings and C stacks; it is not a
collector or OS scheduling theorem. -/
def BuildAllocation.heapGiB (allocation : BuildAllocation) : Nat := 2 * allocation.slots

/-- Repartition only when two asynchronous backends admit more package VMs.
Division truncates unused slots; it never expands the original capacity. -/
def parallelPreparation (allocation : BuildAllocation) : BuildAllocation :=
  let candidates := allocation.slots / 3
  if allocation.packages < candidates then ⟨candidates, 2⟩ else allocation

/-- Repartitioning preserves or lowers the previous declared active capacity. -/
theorem parallelPreparation_slots (allocation : BuildAllocation) :
    (parallelPreparation allocation).slots ≤ allocation.slots := by
  unfold parallelPreparation
  dsimp only
  split
  · simpa [BuildAllocation.slots] using Nat.div_mul_le_self allocation.slots 3
  · exact Nat.le_refl _

/-- More isolated frontends require no larger total declared Scheme heap envelope. -/
theorem parallelPreparation_heap (allocation : BuildAllocation) :
    (parallelPreparation allocation).heapGiB ≤ allocation.heapGiB :=
  Nat.mul_le_mul_left 2 (parallelPreparation_slots allocation)

/-- A selected replacement keeps asynchronous standard backend submission. -/
theorem parallelPreparation_async (allocation : BuildAllocation)
    (changed : allocation.packages < allocation.slots / 3) :
    (parallelPreparation allocation).backends = 2 := by simp [parallelPreparation, changed]

/-- Both standard make's frontend-worker count and its GSC job capacity use the
same per-package setting. Neither aggregate count grows after repartitioning. -/
theorem parallelPreparation_workers (allocation : BuildAllocation) :
    (parallelPreparation allocation).packages * (parallelPreparation allocation).backends ≤
      allocation.packages * allocation.backends := by
  unfold parallelPreparation
  dsimp only
  split
  · have capacity : (allocation.slots / 3) * 3 ≤
        allocation.packages * allocation.backends + allocation.packages := by
      simpa only [BuildAllocation.slots, Nat.mul_add, Nat.mul_one] using
        Nat.div_mul_le_self allocation.slots 3
    change (allocation.slots / 3) * 2 ≤ allocation.packages * allocation.backends
    omega
  · exact Nat.le_refl _

/-- Package capacity never decreases. Execution of the unchanged inventory is
a standard build/runner obligation, checked separately in the real build receipts. -/
theorem parallelPreparation_packages (allocation : BuildAllocation) :
    allocation.packages ≤ (parallelPreparation allocation).packages := by
  unfold parallelPreparation
  dsimp only
  split
  · exact Nat.le_of_lt ‹_›
  · exact Nat.le_refl _

/-- Standard Just workers and Gerbil backend counts on the current machine.
Each compiler session owns a bounded functional part; no shared expander registry
is replaced or cleared. At least one backend remains for small core settings. -/
def boundedPreparation (cores : Nat) : BuildAllocation :=
  if cores < 6 then ⟨1, max 1 (cores - 1)⟩
  else if cores < 9 then ⟨2, max 1 (cores / 2 - 1)⟩
  else if cores < 12 then ⟨3, max 1 (cores / 3 - 1)⟩
  else ⟨4, max 1 (cores / 4 - 1)⟩

/-- Standard concurrent packages are capped at four Just workers; queued
functional parts do not enlarge this capacity. Active capacity stays within cores, apart from the
existing unavoidable frontend/backend pair on a zero/one-core configuration. -/
theorem boundedPreparation_slots (cores : Nat) :
    (boundedPreparation cores).slots ≤ max 2 cores := by
  unfold boundedPreparation
  split
  · simp only [BuildAllocation.slots]; omega
  · split
    · simp only [BuildAllocation.slots]; omega
    · split <;> simp only [BuildAllocation.slots] <;> omega

/-- Sum of configured Scheme heap ceilings, not RSS or live bytes. The package
CLI and compiler frontend are separate processes; C stacks, mappings and CC are excluded. -/
def heapLimitSum (allocation : BuildAllocation) (cli frontend backend : Nat) : Nat :=
  allocation.packages * (cli + frontend + allocation.backends * backend)

/-- The approved two-GiB compiler frontend and unchanged one-GiB CLI fit the
existing root phase's configured ceiling. No physical-memory bound is claimed. -/
theorem boundedPreparation_heap_limits (cores : Nat) :
    heapLimitSum (boundedPreparation cores) 1 2 2 ≤ 4 + 2 * max 1 cores := by
  unfold boundedPreparation
  split
  · simp only [heapLimitSum]; omega
  · split
    · simp only [heapLimitSum]; omega
    · split <;> simp only [heapLimitSum] <;> omega

/-- Per-session visits to a stable common import closure. This counts abstract
preparation requests, not Mach-O mappings, compiler CPU or wall-clock time. -/
def preparationVisits (sessions : Nat) (common : List String) : Nat :=
  sessions * common.eraseDups.length

/-- Fewer bounded compiler sessions reduce repeated common preparation requests;
no purity theorem for arbitrary macros or OS loader-latency bound is asserted. -/
theorem preparationVisits_mono (left right : Nat) (common : List String)
    (fewer : left ≤ right) :
    preparationVisits left common ≤ preparationVisits right common :=
  Nat.mul_le_mul_right common.eraseDups.length fewer

/-- Grouping is scheduling metadata: the ordered declared inventory is retained. -/
def declaredBuildUnits (groups : List (List String)) : List String := groups.flatten

/-- All declared units, including repeated declarations, remain in the inventory;
standard make remains responsible for rejecting duplicate output identities. -/
theorem declaredBuildUnits_count (groups : List (List String)) :
    (declaredBuildUnits groups).length = (groups.map List.length).sum := by
  simp [declaredBuildUnits, List.length_flatten]

/-- Reordering finite declared groups preserves every compile target and its
multiplicity. This is inventory preservation, not equivalence of arbitrary
effectful compiler callbacks or a theorem about their execution time. -/
theorem declaredBuildUnits_perm {left right : List (List String)}
    (order : left.Perm right) :
    (declaredBuildUnits left).Perm (declaredBuildUnits right) := by
  simpa only [declaredBuildUnits] using order.flatten

end LeanPoo.Prototype.Representation
