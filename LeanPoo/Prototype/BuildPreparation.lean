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

/-- Ordered fixture-free cases reuse the standard state monad and List.mapM.
A refusal is a retained result, so the following case still receives the current
state. Independence from module context and absence of hooks/import effects are
premises of this finite model, not inferred properties of Scheme callbacks. -/
def observeSuiteCases {α β ε σ : Type} (modules : List (List (List α)))
    (run : α → StateM σ (Except ε β)) (initial : σ) : List (Except ε β) × σ :=
  (modules.flatten.flatten.mapM run) initial

/-- Coalescing fixture-free module boundaries preserves all ordered results and
final case state, including the state after a failure and later-case execution.
It does not justify coalescing modules with hooks or context-sensitive callbacks. -/
theorem observeSuiteCases_regroup {α β ε σ : Type} (modules : List (List (List α)))
    (run : α → StateM σ (Except ε β)) (initial : σ) :
    observeSuiteCases [modules.flatten] run initial = observeSuiteCases modules run initial := by
  simp [observeSuiteCases]

/-- Lexical expansion may remove transformer metadata only when every case keeps
its complete state/result behavior. Existing module/suite boundaries and ordered
refusals are preserved; this premise does not verify the Gerbil expander. -/
theorem observeSuiteCases_expansion {α β ε σ : Type} (modules : List (List (List α)))
    (before after : α → StateM σ (Except ε β))
    (same : ∀ input state, before input state = after input state) (initial : σ) :
    observeSuiteCases modules before initial = observeSuiteCases modules after initial := by
  have equal : before = after := by funext input state; exact same input state
  rw [equal]

/-- A checked distinct image inventory already has the standard deduplicated
form. This counts declared names, not paths, mappings or operating-system work. -/
theorem uniquePreparationNames (names : List String) (distinct : names.Nodup) :
    names.eraseDups = names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have hd := List.nodup_cons.mp distinct
    have filtered : rest.filter (fun other => !other == name) = rest := by
      apply List.filter_eq_self.mpr
      intro other member
      have different : other ≠ name := fun same => hd.1 (same ▸ member)
      simp [different]
    rw [List.eraseDups_cons, filtered, ih hd.2]

/-- Abstract observations of standard make's declared outputs and runtime
admission. A fresh interface/static marker alone does not certify its backend
image. This is a ghost state, not a Scheme-side cache or output registry. -/
structure BuildOutputs where
  declaredFresh : Bool
  runtimeReady : Bool
  deriving DecidableEq, Repr

/-- Standard clean invalidates declared freshness; it need not erase every
numbered runtime object. Successful cleanup is a premise of this transition. -/
def BuildOutputs.invalidate (outputs : BuildOutputs) : BuildOutputs :=
  { outputs with declaredFresh := false }

/-- The existing make freshness decision must request compilation again. -/
def BuildOutputs.needsBuild (outputs : BuildOutputs) : Bool := !outputs.declaredFresh

/-- Cleaning after refused preparation prevents reusing a surviving marker. -/
theorem BuildOutputs.invalidate_requires_build (outputs : BuildOutputs) :
    outputs.invalidate.needsBuild = true := rfl

/-- Invalidating the marker is not evidence that a runtime image was repaired. -/
theorem BuildOutputs.invalidate_runtime (outputs : BuildOutputs) :
    outputs.invalidate.runtimeReady = outputs.runtimeReady := rfl

/-- A cache hit and missing runtime image can coexist after interrupted output.
Loader/test receipts must therefore remain independent of make's freshness test. -/
theorem BuildOutputs.fresh_not_runtime :
    ∃ outputs : BuildOutputs, outputs.needsBuild = false ∧ outputs.runtimeReady = false :=
  ⟨⟨true, false⟩, rfl, rfl⟩

/-- Merge only an adjacent functional group, retaining the untouched prefix and
suffix. Ordered results and final state are preserved even when earlier cases
refuse. As above, module fixtures and initialization effects are excluded. -/
theorem observeSuiteCases_regroup_between {α β ε σ : Type}
    (before group after : List (List (List α)))
    (run : α → StateM σ (Except ε β)) (initial : σ) :
    observeSuiteCases (before ++ [group.flatten] ++ after) run initial =
      observeSuiteCases (before ++ group ++ after) run initial := by
  simp [observeSuiteCases, List.flatten_append]

/-- Exact source observations for an explicitly declared build footprint. The
caller must include compiler identity, flags and transitive build inputs; this
model neither discovers dependencies nor assumes a cryptographic hash injective. -/
def sameBuildInputs {α : Type} (required : List String) (before after : String → α) : Prop :=
  ∀ file ∈ required, before file = after file

/-- Revising only inputs outside the library footprint preserves its exact key
observations. This says nothing about omitting the revised tests: their own build
and complete execution remain separate acceptance obligations. -/
theorem sameBuildInputs_private_revision {α : Type} (required : List String)
    (before after : String → α) (changed : List String)
    (separate : ∀ file ∈ required, file ∉ changed)
    (stable : ∀ file, file ∉ changed → before file = after file) :
    sameBuildInputs required before after := by
  intro file needed
  exact stable file (separate file needed)

/-- A changed required input rejects reuse, even if that input is a test-directory
build helper. Directory labels alone cannot establish dependency independence. -/
theorem sameBuildInputs_required_revision {α : Type} (required : List String)
    (before after : String → α) (file : String)
    (needed : file ∈ required) (changed : before file ≠ after file) :
    ¬ sameBuildInputs required before after := by
  intro same
  exact changed (same file needed)

/-- Abstract cumulative CPU counters in one common unit. These exact laws do
not verify Gambit's floating-point measurements or assign wall residuals to dyld. -/
structure ProcessCounters where
  cpu : Nat
  gcCpu : Nat
  deriving DecidableEq, Repr

/-- GC work is included in total process CPU, rather than an additional cost. -/
def ProcessCounters.Valid (stats : ProcessCounters) : Prop := stats.gcCpu ≤ stats.cpu

/-- Subtract only counters admitted as monotone in both GC and non-GC work.
Valid individual snapshots and monotone total CPU alone do not justify this
partition: an inconsistent delta must be rejected, never clamped to zero. -/
theorem ProcessCounters.delta_partition (before after : ProcessCounters)
    (beforeValid : before.Valid) (afterValid : after.Valid)
    (gcMonotone : before.gcCpu ≤ after.gcCpu)
    (nonGcMonotone : before.cpu - before.gcCpu ≤ after.cpu - after.gcCpu) :
    after.cpu - before.cpu = (after.gcCpu - before.gcCpu) +
      ((after.cpu - after.gcCpu) - (before.cpu - before.gcCpu)) := by
  unfold ProcessCounters.Valid at beforeValid afterValid
  omega

/-- Clock observations at public process/progress boundaries. Ticks are exact;
the host clock and faithful delivery of these observations remain premises. -/
structure CheckPhaseTimes where
  started : Nat
  testStarted : Nat
  harnessStarted : Nat
  harnessFinished : Nat
  reported : Nat
  testExited : Nat
  eof : Nat
  finished : Nat
  deriving DecidableEq, Repr

/-- Missing/reversed boundaries cannot be repaired by clamping elapsed time. -/
def CheckPhaseTimes.Valid (times : CheckPhaseTimes) : Prop :=
  times.started ≤ times.testStarted ∧ times.testStarted ≤ times.harnessStarted ∧
  times.harnessStarted ≤ times.harnessFinished ∧ times.harnessFinished ≤ times.reported ∧
  times.reported ≤ times.testExited ∧ times.testExited ≤ times.eof ∧ times.eof ≤ times.finished

instance (times : CheckPhaseTimes) : Decidable times.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- Build, import/init, test execution, report, post-report exit, studies and reap
windows are observations; none is automatically an exclusive dyld/GC cost. -/
def CheckPhaseTimes.intervals (times : CheckPhaseTimes) : List Nat :=
  [times.testStarted - times.started, times.harnessStarted - times.testStarted,
   times.harnessFinished - times.harnessStarted, times.reported - times.harnessFinished,
   times.testExited - times.reported, times.eof - times.testExited, times.finished - times.eof]

/-- All admitted windows telescope to the complete command; no residual is
dropped merely because it occurred after the last successful case. -/
theorem CheckPhaseTimes.total (times : CheckPhaseTimes) (valid : times.Valid) :
    times.intervals.sum = times.finished - times.started := by
  simp only [CheckPhaseTimes.intervals, List.sum_cons, List.sum_nil]
  unfold CheckPhaseTimes.Valid at valid
  omega

/-- Preserve the observed admission order: incomplete execution refuses first,
then missing clocks, then nonmonotone observations. No success is fabricated. -/
def admitCheckTimes (times : Option CheckPhaseTimes) (modules begun passed : Nat) :
    Except String (List Nat) :=
  if 0 < modules ∧ 0 < begun ∧ begun = passed then
    match times with
    | none => .error "missing check phase"
    | some times => if times.Valid then .ok times.intervals else .error "nonmonotone check observation"
  else .error "incomplete check observation"

/-- An admitted receipt has complete case delivery and a partition of the full
observed lifetime. This is not authentication of IO origin or a latency bound. -/
theorem admitCheckTimes_complete (candidate : Option CheckPhaseTimes) (modules begun passed : Nat)
    (spans : List Nat) (accepted : admitCheckTimes candidate modules begun passed = .ok spans) :
    ∃ times, candidate = some times ∧ times.Valid ∧
      spans.sum = times.finished - times.started ∧ begun = passed ∧ 0 < modules ∧ 0 < begun := by
  unfold admitCheckTimes at accepted
  by_cases counts : 0 < modules ∧ 0 < begun ∧ begun = passed
  · rw [ite_eq_left counts] at accepted
    cases candidate with
    | none => cases accepted
    | some times =>
      change (if times.Valid then Except.ok times.intervals else Except.error "nonmonotone check observation") = .ok spans at accepted
      by_cases valid : times.Valid
      · rw [ite_eq_left valid] at accepted
        cases accepted
        exact ⟨times, rfl, valid, times.total valid, counts.2.2, counts.1, counts.2.1⟩
      · rw [ite_eq_right valid] at accepted
        cases accepted
  · rw [ite_eq_right counts] at accepted
    cases accepted

/-- Each compiler context pays its common closure and demands an optional
exclusive closure only when used. Weights must come from the standard compiler's
actual dependency observation; these are source work units, not elapsed time. -/
def optionalPreparation (common extra : Nat) (requests : List Bool) : Nat :=
  (requests.map (fun requested => common + if requested then extra else 0)).sum

/-- Removing an eager optional edge saves exactly the unused contexts' exclusive
preparation. Shared dependencies belong in `common`, not in `extra`. In particular,
a complete workflow that requests the feature everywhere saves no work here. -/
theorem optionalPreparation_partition (common extra : Nat) (requests : List Bool) :
    requests.length * (common + extra) = optionalPreparation common extra requests +
      (requests.filter (! ·)).length * extra := by
  induction requests with
  | nil => simp [optionalPreparation]
  | cons requested rest ih =>
    cases requested <;>
      simp [optionalPreparation, Nat.add_mul] at * <;> omega

/-- Demand-driven preparation never enlarges the same declared context work. -/
theorem optionalPreparation_le (common extra : Nat) (requests : List Bool) :
    optionalPreparation common extra requests ≤ requests.length * (common + extra) := by
  rw [optionalPreparation_partition]
  omega

/-- Complete source work includes unchanged execution plus the additional IO
routing. The caller must budget action closures, argument rows, current-binding
lookup and any extra standard loader-stub admissions; metadata savings alone are insufficient.
All terms use one declared cost unit, not an inferred physical/GC time bound. -/
def optionalWorkflowWork (common extra : Nat) (requests : List Bool)
    (execution routing : Nat) : Nat :=
  optionalPreparation common extra requests + execution + routing

/-- A demand-driven boundary improves the declared complete workflow exactly
when avoided preparation pays for its additional routing. This is also the
negative control: fewer eager dependencies cannot justify an unbounded wrapper. -/
theorem optionalWorkflowWork_le_iff (common extra : Nat) (requests : List Bool)
    (execution routing : Nat) :
    optionalWorkflowWork common extra requests execution routing ≤
      requests.length * (common + extra) + execution ↔
      routing ≤ (requests.filter (! ·)).length * extra := by
  have balance := optionalPreparation_partition common extra requests
  unfold optionalWorkflowWork
  omega

/-- Gambit's documented guard when single-host generation was requested.
Zero leaves the request unbounded; exceeding a positive label limit selects
multiple C hosts. This models policy, not correctness of a C compiler. -/
def singleHostEnabled (limit labels : Nat) : Bool := decide (limit = 0 ∨ labels ≤ limit)

/-- The default zero limit does not bound the size of a requested host graph. -/
theorem singleHostEnabled_unbounded (labels : Nat) : singleHostEnabled 0 labels = true := by
  simp [singleHostEnabled]

/-- A strict positive cutoff rejects exactly the oversized single host. -/
theorem singleHostEnabled_exceeded (limit labels : Nat)
    (positive : 0 < limit) (large : limit < labels) : singleHostEnabled limit labels = false := by
  simp [singleHostEnabled]; omega

/-- Small modules retain the requested optimized layout without a blanket change. -/
theorem singleHostEnabled_small (limit labels : Nat) (small : labels ≤ limit) :
    singleHostEnabled limit labels = true := by simp [singleHostEnabled, small]

/-- A positive admitted limit certifies the actual label bound. -/
theorem singleHostEnabled_bound (limit labels : Nat) (positive : 0 < limit)
    (accepted : singleHostEnabled limit labels = true) : labels ≤ limit := by
  simp only [singleHostEnabled, decide_eq_true_eq] at accepted
  omega

/-- The declared within-host ordered-label-pair potential. It is a structural
metric, not a claim that GCC spends one instruction or byte per pair. -/
def hostPairPotential (labels : Nat) : Nat := labels * labels

/-- Splitting a graph removes cross-host label pairs from this local potential.
Actual host partitioning belongs to the standard backend and is a host premise. -/
theorem hostPairPotential_split (left right : Nat) :
    hostPairPotential left + hostPairPotential right ≤ hostPairPotential (left + right) := by
  simp only [hostPairPotential, Nat.add_mul, Nat.mul_add]
  omega

/-- Routing is charged explicitly: partitioning improves this declared metric
only when its extra boundary cost fits the removed cross-host pairs. This is
not a wall-clock prediction or a complexity theorem about GCC. -/
theorem hostPairPotential_routing (left right routing : Nat) :
    hostPairPotential left + hostPairPotential right + routing ≤
      hostPairPotential (left + right) ↔ routing ≤ 2 * left * right := by
  simp only [hostPairPotential, Nat.add_mul, Nat.mul_add, Nat.mul_comm right left,
    Nat.mul_assoc, Nat.two_mul]
  omega

/-- Complete child CPU includes work from descendants not yet reaped. Units are
nonnegative logical ticks; parallel CPU and wall clocks are separate quantities. -/
def totalChildCpu (reaped outstanding : Nat) : Nat := reaped + outstanding

/-- A terminated process-tree receipt can be only a lower bound, never a complete
CPU decomposition unless outstanding descendants have all been accounted for. -/
theorem reportedChildCpu_lower (reaped outstanding : Nat) :
    reaped ≤ totalChildCpu reaped outstanding := by simp [totalChildCpu]

/-- The completed/reaped case admits exact accounting. -/
theorem reportedChildCpu_complete (reaped : Nat) : totalChildCpu reaped 0 = reaped := by
  simp [totalChildCpu]

/-- Zero collected CPU cannot certify idle waiting while work remains uncollected. -/
theorem reportedChildCpu_not_idle (outstanding : Nat) (busy : 0 < outstanding) :
    0 < totalChildCpu 0 outstanding := by simpa [totalChildCpu] using busy

end LeanPoo.Prototype.Representation
