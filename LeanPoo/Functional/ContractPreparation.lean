import LeanPoo.Functional.ContractConstruction

namespace LeanPoo.Functional.ContractFamily
/-- Explicit operation weights, never a wall-clock or allocator axiom. -/
structure PreparationCosts where
  prepareCost : Nat
  sharedCost : Nat
  directCost : Nat
  selectionCost : Nat
  deriving Repr

namespace PreparationCosts
/-- The two existing implementations of closed projection: shared preparation or direct access. -/
inductive Strategy where | shared | direct deriving BEq, DecidableEq, Repr

/-- Modeled shared work for keys: one preparation plus one shared projection per key.
Weights are supplied explicitly; this is not a measured time or allocation count. -/
def shared (costs : PreparationCosts) (keys : Nat) := costs.prepareCost + keys * costs.sharedCost
/-- Modeled direct projection work for keys, excluding selector cost.
Callers add selection/setup/guard costs at their actual execution frequency. -/
def direct (costs : PreparationCosts) (keys : Nat) := keys * costs.directCost

/-- Choose direct only when its saving strictly pays selectionCost; ties use shared.
Both branches still require the same closed projection semantics and admission checks. -/
def choose (costs : PreparationCosts) (keys : Nat) : Strategy :=
  if costs.selectionCost + costs.direct keys < costs.shared keys then .direct else .shared

/-- Charge one selector call plus the chosen direct/shared projection work.
The shared fallback also pays the selector, so it may exceed unconditional shared work. -/
def selected (costs : PreparationCosts) (keys : Nat) :=
  costs.selectionCost + match costs.choose keys with
    | .shared => costs.shared keys
    | .direct => costs.direct keys

/-- If direct is chosen, its projection work plus selection fits the shared budget. -/
theorem direct_covered (costs : PreparationCosts) (keys : Nat)
    (chosen : costs.choose keys = .direct) : costs.selected keys ≤ costs.shared keys := by
  unfold choose at chosen
  split at chosen
  · rename_i saving
    simp only [selected, choose, ite_eq_left saving]
    exact Nat.le_of_lt saving
  · contradiction

/-- The fallback still pays for selection: no free-selector claim. -/
theorem selected_bound (costs : PreparationCosts) (keys : Nat) :
    costs.selected keys ≤ costs.selectionCost + costs.shared keys := by
  by_cases saving : costs.selectionCost + costs.direct keys < costs.shared keys
  · simp [selected, choose, saving]
    omega
  · simp [selected, choose, saving]

/-- A certified choice at one support size under fixed immutable prices.
It caches no dependency graph, contract descriptor or approval; arity changes reselect. -/
structure SelectionCache (costs : PreparationCosts) where
  keys : Nat
  strategy : Strategy
  origin : strategy = costs.choose keys

/-- Compute and certify the cold choice for the supplied support size.
Its one selector call and cache setup must be charged by the amortization model. -/
def cacheSelection (costs : PreparationCosts) (keys : Nat) : SelectionCache costs := ⟨keys,costs.choose keys,rfl⟩

/-- Return the ordinary strategy and zero/one additional selector executions.
Equal arity reuses the certified choice; other arities select with the same prices.
Support guards and cache allocation are charged separately, not treated as free. -/
def SelectionCache.select (prepared : SelectionCache costs) (keys : Nat) : Strategy × Nat :=
  if keys = prepared.keys then (prepared.strategy,0) else (costs.choose keys,1)

/-- Every cache hit and fallback returns the same strategy as ordinary selection. -/
theorem SelectionCache.select_eq (prepared : SelectionCache costs) (keys : Nat) :
    (prepared.select keys).1 = costs.choose keys := by
  by_cases same : keys = prepared.keys
  · simp [SelectionCache.select, same, prepared.origin]
  · simp [SelectionCache.select, same]

/-- At the certified arity, reuse the choice and execute no additional selector. -/
theorem SelectionCache.hit (prepared : SelectionCache costs) :
    prepared.select prepared.keys = (prepared.strategy,0) := by simp [SelectionCache.select]

/-- At another arity, run the ordinary selector once and return its current-size choice. -/
theorem SelectionCache.miss (prepared : SelectionCache costs) (keys : Nat) (different : keys ≠ prepared.keys) :
    prepared.select keys = (costs.choose keys,1) := by simp [SelectionCache.select,different]

/-- Compare selector execution only: same projections and publication remain required.
One cache construction call plus all fallback selections are charged across the revision list. -/
def SelectionCache.selections (prepared : SelectionCache costs) (sizes : List Nat) : Nat :=
  1 + (sizes.map fun keys => (prepared.select keys).2).sum

/-- Stable arity incurs exactly the one cold selector call across all revisions. -/
theorem SelectionCache.stable_selections (prepared : SelectionCache costs) (revisions : Nat) :
    prepared.selections (List.replicate revisions prepared.keys) = 1 := by
  simp [SelectionCache.selections, SelectionCache.select]

/-- For at least one revision, stable-cache selector charges fit repeated selection.
This selector-only bound does not yet include setup or per-revision guards. -/
theorem SelectionCache.amortized (prepared : SelectionCache costs) (revisions : Nat) (nonempty : 1 ≤ revisions) :
    prepared.selections (List.replicate revisions prepared.keys) * costs.selectionCost ≤ revisions * costs.selectionCost := by
  rw [prepared.stable_selections]
  simpa using Nat.mul_le_mul_right costs.selectionCost nonempty

/-- Actual stage counts are supplied by native traces and semantic admission.
A changed generic/contract is never approved by a cheaper projection policy alone. -/
structure PublicationCosts where
  capture : Nat
  construct : Nat
  bind : Nat
  generic : Nat
  approve : Nat
  deriving Repr

/-- Charge context capture, preparation, descriptor construction, wrapper binding,
generic construction and approval probes at the supplied actual stage counts.
Allocation/collection and cache setup remain separate explicit costs. -/
def PublicationCosts.total (prices : PublicationCosts) (preparation built bound generics probes : Nat) :=
  prices.capture + preparation + built * prices.construct + bound * prices.bind +
    generics * prices.generic + probes * prices.approve

/-- Replacing only coherent projection work by a covered direct choice lowers
or preserves the modeled publication total when every other stage count stays equal. -/
theorem publication_direct_bound (costs : PreparationCosts) (keys : Nat)
    (chosen : costs.choose keys = .direct) (prices : PublicationCosts) (built bound generics probes : Nat) :
    prices.total (costs.selected keys) built bound generics probes ≤
      prices.total (costs.shared keys) built bound generics probes := by
  unfold PublicationCosts.total
  have h := costs.direct_covered keys chosen
  omega
/-- Native shared expansion removes one reconstruction and two per-key adapters.
The weights include reconstructed representation allocation; binding/registration
and approval remain in the unchanged publication base. guard charges the extra
registration-provenance callback and any added protocol lookup per changed key. -/
structure ExpansionCosts where
  expand : Nat
  adapter : Nat
  guard : Nat
  deriving Repr

/-- Reference expansion charge for actual changed keys; retained keys cost zero. -/
def ExpansionCosts.separate (prices : ExpansionCosts) (changed : Nat) :=
  changed * (2 * prices.expand + 2 * prices.adapter)

/-- Shared expansion charge for the same changed keys, including the extra guard; no constructor adapters. -/
def ExpansionCosts.shared (prices : ExpansionCosts) (changed : Nat) := changed * (prices.expand + prices.guard)

/-- Exact modeled saving is conditional on these native call/allocation weights. -/
theorem ExpansionCosts.saving (prices : ExpansionCosts) (changed : Nat) :
    prices.separate changed + changed * prices.guard =
      prices.shared changed + changed * (prices.expand + 2 * prices.adapter) := by
  simp only [ExpansionCosts.separate, ExpansionCosts.shared, Nat.mul_add,
    Nat.mul_left_comm changed 2 prices.expand, Nat.mul_left_comm changed 2 prices.adapter]
  omega

/-- Binding, method registration and joint approval are not removed from the base.
Only the expansion term changes; no unconditional wall-time improvement follows. -/
theorem ExpansionCosts.publication_bound (prices : ExpansionCosts) (changed base : Nat)
    (covered : prices.guard ≤ prices.expand + 2 * prices.adapter) :
    base + prices.shared changed ≤ base + prices.separate changed := by
  have paid := Nat.mul_le_mul_left changed covered
  have saving := prices.saving changed
  omega

/-- A separate collection charge prevents projecting a primitive-cost bound onto
measured total CPU when the two executions have different collection histories. -/
def withCollections (core collectionPrice collections : Nat) := core + collectionPrice * collections

/-- Extend the projection/publication bound when selected collection count is
no greater; collector prices are assumptions rather than native guarantees. -/
theorem publication_collection_bound (costs : PreparationCosts) (keys : Nat)
    (chosen : costs.choose keys = .direct) (prices : PublicationCosts) (built bound generics probes : Nat)
    (collectionPrice selectedCollections sharedCollections : Nat)
    (within : selectedCollections ≤ sharedCollections) :
    withCollections (prices.total (costs.selected keys) built bound generics probes) collectionPrice selectedCollections ≤
    withCollections (prices.total (costs.shared keys) built bound generics probes) collectionPrice sharedCollections :=
  Nat.add_le_add (costs.publication_direct_bound keys chosen prices built bound generics probes)
    (Nat.mul_le_mul_left collectionPrice within)

/-- More generally, a core saving can pay a collection excess, but this is an
additional budget premise rather than a consequence of choosing direct. -/
theorem collection_budget_bound (selected shared collectionPrice selectedCollections sharedCollections : Nat)
    (core : selected ≤ shared)
    (paid : collectionPrice * selectedCollections - collectionPrice * sharedCollections ≤ shared - selected) :
    withCollections selected collectionPrice selectedCollections ≤ withCollections shared collectionPrice sharedCollections := by
  unfold withCollections
  omega

/-- An expansion saving pays GC excess only under an explicit measured budget.
Neither pure sharing nor fewer adapter allocations establishes collector behavior. -/
theorem ExpansionCosts.collection_bound (prices : ExpansionCosts) (changed base : Nat)
    (covered : prices.guard ≤ prices.expand + 2 * prices.adapter)
    (collectionPrice selectedCollections referenceCollections : Nat)
    (paid : collectionPrice * selectedCollections - collectionPrice * referenceCollections ≤
      prices.separate changed - prices.shared changed) :
    withCollections (base + prices.shared changed) collectionPrice selectedCollections ≤
      withCollections (base + prices.separate changed) collectionPrice referenceCollections := by
  have core := prices.publication_bound changed base covered
  have budget : collectionPrice * selectedCollections - collectionPrice * referenceCollections ≤
      (base + prices.separate changed) - (base + prices.shared changed) := by omega
  exact collection_budget_bound _ _ _ _ _ core budget

/-- Observed CPU and GC charges have explicit validity before subtraction.
These model observations, not an implementation of the collector or a heap reset. -/
structure Observation where
  cpu : Nat
  gc : Nat
  within : gc ≤ cpu

/-- Subtract the observed GC charge from CPU under Observation.within.
The residual is accounting only, not proof of identical heaps or primitive work. -/
def Observation.core (observation : Observation) := observation.cpu - observation.gc

/-- Under valid observations, CPU decomposes exactly into residual CPU plus GC CPU. -/
theorem Observation.decompose (observation : Observation) :
    observation.cpu = observation.core + observation.gc := (Nat.sub_add_cancel observation.within).symm

/-- Decompose EACH pair. Medians of independently ordered phases do not inherit
this identity; the native driver reports paired deltas before taking a median. -/
theorem paired_delta (baseline selected : Observation) :
    (selected.cpu : Int) - baseline.cpu =
      ((selected.core : Int) - baseline.core) + ((selected.gc : Int) - baseline.gc) := by
  have hb := baseline.decompose
  have hs := selected.decompose
  omega

/-- ABBA balances an additive first/second-position term; real process drift need
not be additive, so order balance is a protocol control, not timing equivalence. -/
theorem balanced_order (difference order : Int) :
    (difference + order) + (difference - order) +
      (difference - order) + (difference + order) = 4 * difference := by omega

/-- Include once-only template validation before amortizing specialization. -/
structure TemplateCosts where
  setup : Nat
  specialize : Nat
  rebuild : Nat
  deriving Repr

/-- Cold/shared specialization mode; a fresh path allocates no shared check record. -/
inductive CheckMode where | fresh | shared deriving BEq, DecidableEq, Repr

/-- Include first compilation/setup before deciding to share immutable checks. -/
def TemplateCosts.sharedTotal (costs : TemplateCosts) (revisions : Nat) := costs.setup + revisions * costs.specialize

/-- Ordinary fresh rebuilding remains the reference, including zero revisions. -/
def TemplateCosts.freshTotal (costs : TemplateCosts) (revisions : Nat) := revisions * costs.rebuild

/-- Compile the check strategy once for a supplied horizon; ties keep fresh. -/
def TemplateCosts.choose (costs : TemplateCosts) (revisions : Nat) : CheckMode :=
  if costs.sharedTotal revisions < costs.freshTotal revisions then .shared else .fresh

/-- Cost of the configured mode excludes neither first compilation nor guard work. -/
def TemplateCosts.selectedTotal (costs : TemplateCosts) (revisions : Nat) :=
  match costs.choose revisions with | .fresh => costs.freshTotal revisions | .shared => costs.sharedTotal revisions

/-- Conditional operation-budget guarantee; this does not assert native elapsed time. -/
theorem TemplateCosts.selected_bound (costs : TemplateCosts) (revisions : Nat) :
    costs.selectedTotal revisions ≤ costs.freshTotal revisions := by
  by_cases cheap : costs.sharedTotal revisions < costs.freshTotal revisions
  · simpa [selectedTotal, choose, cheap] using Nat.le_of_lt cheap
  · simp [selectedTotal, choose, cheap]

/-- Choosing a check mode has its own configuration cost, independent of the
shared-record setup. Admit that fee only when actual modeled saving covers it. -/
theorem TemplateCosts.configuration_covered (costs : TemplateCosts) (uses configurationCost base : Nat)
    (paid : configurationCost ≤ costs.freshTotal uses - costs.selectedTotal uses) :
    base + configurationCost + costs.selectedTotal uses ≤ base + costs.freshTotal uses := by
  have selected := costs.selected_bound uses
  omega

/-- A single cold use cannot amortize a setup at least as large as its saving. -/
theorem TemplateCosts.cold (costs : TemplateCosts) (unpaid : costs.rebuild ≤ costs.setup + costs.specialize) :
    costs.choose 1 = .fresh := by simp [choose, sharedTotal, freshTotal, Nat.not_lt.mpr unpaid]

theorem template_amortized (costs : TemplateCosts) (revisions : Nat)
    (cheaper : costs.specialize ≤ costs.rebuild)
    (paid : costs.setup ≤ revisions * (costs.rebuild - costs.specialize)) :
    costs.setup + revisions * costs.specialize ≤ revisions * costs.rebuild := by
  calc
    costs.setup + revisions * costs.specialize ≤
        revisions * (costs.rebuild - costs.specialize) + revisions * costs.specialize := Nat.add_le_add_right paid _
    _ = revisions * ((costs.rebuild - costs.specialize) + costs.specialize) := (Nat.mul_add _ _ _).symm
    _ = revisions * costs.rebuild := by rw [Nat.sub_add_cancel cheaper]

/-- Cache allocation/setup and each support guard are charged in addition to the
one cold selector call. Stable selector reuse alone does not make cache construction free. -/
structure SelectionCacheCosts where
  setup : Nat
  guard : Nat
  deriving Repr

/-- Charge cache setup, the cold and fallback selector calls, and every support guard
for the given arity sequence. Projection and publication work are not included. -/
def SelectionCache.totalCost (prepared : SelectionCache costs) (prices : SelectionCacheCosts) (sizes : List Nat) :=
  prices.setup + prepared.selections sizes * costs.selectionCost + sizes.length * prices.guard

/-- Stable support removes fallback calls but still pays setup, cold selection and all guards. -/
theorem SelectionCache.stable_total (prepared : SelectionCache costs) (prices : SelectionCacheCosts) (revisions : Nat) :
    prepared.totalCost prices (List.replicate revisions prepared.keys) =
      prices.setup + costs.selectionCost + revisions * prices.guard := by
  simp [SelectionCache.totalCost, prepared.stable_selections]

/-- A stable cache fits repeated selector cost only if guard cost is no larger
and enough revisions repay setup plus the cold choice. No unconditional speedup follows. -/
theorem SelectionCache.total_amortized (prepared : SelectionCache costs) (prices : SelectionCacheCosts) (revisions : Nat)
    (cheaper : prices.guard ≤ costs.selectionCost)
    (paid : prices.setup + costs.selectionCost ≤ revisions * (costs.selectionCost - prices.guard)) :
    prepared.totalCost prices (List.replicate revisions prepared.keys) ≤ revisions * costs.selectionCost := by
  rw [prepared.stable_total]
  exact template_amortized ⟨prices.setup + costs.selectionCost, prices.guard, costs.selectionCost⟩ revisions cheaper paid

/-- Count actual changed-context selector entries, not every publication. Extra
collections are a conservative budget above the dynamic reference. These are
conditional cost inputs, not predictions certified by a model label. -/
structure SelectionBudget where
  calls : Nat
  fallbacks : Nat
  collectionPrice : Nat
  extraCollections : Nat
  deriving Repr

/-- Selector implementation choice; projection meaning and metadata do not change. -/
inductive SelectionMode where | dynamic | cached deriving BEq, DecidableEq, Repr

/-- Reference selector cost at the actual preparation-miss count. -/
def SelectionCacheCosts.dynamicBudget (_costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) := budget.calls * selectionCost

/-- Charge setup, cold/fallback selections, every support guard and extra GC. -/
def SelectionCacheCosts.cachedBudget (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) := costs.setup + (1 + budget.fallbacks) * selectionCost +
      budget.calls * costs.guard + budget.collectionPrice * budget.extraCollections

/-- Reuse selection only if the complete supported budget strictly improves.
Ties keep ordinary selection and do not allocate/force an unused cache. -/
def SelectionCacheCosts.choose (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) : SelectionMode :=
  if costs.cachedBudget selectionCost budget < costs.dynamicBudget selectionCost budget then .cached else .dynamic

/-- Native callback captures the immutable fixed term once, validating only the
selection-cost argument on each call. Reassociation changes no chosen mode. -/
def SelectionCacheCosts.compiledChoice (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) : SelectionMode :=
  let fixed := costs.setup + budget.calls * costs.guard + budget.collectionPrice * budget.extraCollections
  if fixed + (1 + budget.fallbacks) * selectionCost < budget.calls * selectionCost then .cached else .dynamic

/-- Hoisted fixed arithmetic is exactly the original conditional choice, for all
supported costs and horizons; no empirical constants enter this identity. -/
theorem SelectionCacheCosts.compiled_eq (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) : costs.compiledChoice selectionCost budget = costs.choose selectionCost budget := by
  simp [compiledChoice, choose, cachedBudget, dynamicBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Total selector budget for the selected mode; other pipeline stages stay explicit. -/
def SelectionCacheCosts.selectedBudget (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) := match costs.choose selectionCost budget with
  | .dynamic => costs.dynamicBudget selectionCost budget
  | .cached => costs.cachedBudget selectionCost budget

/-- Budgeted choice cannot exceed ordinary selection under the supplied premises. -/
theorem SelectionCacheCosts.selected_bound (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) : costs.selectedBudget selectionCost budget ≤ costs.dynamicBudget selectionCost budget := by
  by_cases cheaper : costs.cachedBudget selectionCost budget < costs.dynamicBudget selectionCost budget
  · simpa [selectedBudget, choose, cheaper] using Nat.le_of_lt cheaper
  · simp [selectedBudget, choose, cheaper]

/-- Descriptor construction, binding, generic expansion and joint approval are
preserved in base. Shared expansion alone does not justify a zero-GC selector price. -/
theorem SelectionCacheCosts.workflow_bound (costs : SelectionCacheCosts) (selectionCost base : Nat)
    (budget : SelectionBudget) : base + costs.selectedBudget selectionCost budget ≤
      base + costs.dynamicBudget selectionCost budget := Nat.add_le_add_left (costs.selected_bound selectionCost budget) base

/-- Compiling a policy into a source is a real one-time configuration cost.
Its amortization must be paid from the selector saving; dynamic fallback alone
cannot prove a cost-free factory. Native configuration and repeated cold source
construction therefore have distinct benchmark scenarios. -/
theorem SelectionCacheCosts.configuration_covered (costs : SelectionCacheCosts)
    (selectionCost configurationCost base : Nat) (budget : SelectionBudget)
    (paid : configurationCost ≤ costs.dynamicBudget selectionCost budget - costs.selectedBudget selectionCost budget) :
    base + configurationCost + costs.selectedBudget selectionCost budget ≤
      base + costs.dynamicBudget selectionCost budget := by
  have selected := costs.selected_bound selectionCost budget
  omega

/-- No preparation miss implies dynamic mode, even if all supplied weights are zero. -/
theorem SelectionCacheCosts.no_calls (costs : SelectionCacheCosts) (selectionCost : Nat)
    (budget : SelectionBudget) (empty : budget.calls = 0) : costs.choose selectionCost budget = .dynamic := by
  simp [choose, dynamicBudget, empty]

/-- Supplied primitive work for effective-method construction and cache transport.
resolve is additional cold sparse lookup; hit includes per-call shape/cache work.
These weights are not native timings, and extra GC is charged explicitly. -/
structure EffectiveCosts where
  prepare : Nat
  resolve : Nat
  hit : Nat
  invoke : Nat
  transport : Nat
  allocation : Nat
  collectionPrice : Nat
  deriving Repr

/-- Actual nested invocation horizon. Cold resolutions include guarded cold
shapes; compilation events are unguarded misses plus EVERY guarded call. Edits
and eviction enter the miss counts instead of being assumed away. -/
structure EffectiveBudget where
  calls : Nat
  coldResolutions : Nat
  unguardedMisses : Nat
  guardedCalls : Nat
  extraCollections : Nat
  deriving Repr

/-- Reuse the existing template decision: include allocation, cold sparse lookup,
all compilation events and excess GC before charging each hit/invoke/transport.
The fresh reference discards nested successors and repeats resolution/preparation. -/
def EffectiveCosts.prices (costs : EffectiveCosts) (budget : EffectiveBudget) : TemplateCosts :=
  ⟨costs.allocation + budget.coldResolutions * costs.resolve +
    (budget.unguardedMisses + budget.guardedCalls) * costs.prepare +
    budget.extraCollections * costs.collectionPrice,
   costs.hit + costs.invoke + costs.transport,
   costs.hit + costs.resolve + costs.prepare + costs.invoke⟩

/-- Guards are not hidden in a warm-hit estimate. Every guarded call pays one
compilation even when candidate lookup hits, as proved by call_guarded. -/
def EffectiveBudget.compilations (budget : EffectiveBudget) := budget.unguardedMisses + budget.guardedCalls

/-- Disjoint guarded calls and unconditional misses bound compilation work by
actual calls. No such premise is inferred from a C4 shape or old measurement. -/
theorem EffectiveBudget.compilations_bound (budget : EffectiveBudget)
    (accounted : budget.unguardedMisses + budget.guardedCalls ≤ budget.calls) :
    budget.compilations ≤ budget.calls := accounted

/-- Joint construction, binding, contract checks and approval stay in base.
The chosen operation budget includes first compilation and transport, and is
bounded by the value-only nested reference under the supplied counters/weights. -/
theorem EffectiveCosts.workflow_bound (costs : EffectiveCosts) (budget : EffectiveBudget) (base : Nat) :
    base + (costs.prices budget).selectedTotal budget.calls ≤
      base + (costs.prices budget).freshTotal budget.calls :=
  Nat.add_le_add_left ((costs.prices budget).selected_bound budget.calls) base

/-- One cold unconditional invocation cannot repay cache allocation/transport;
its setup already includes the same sparse resolution and compilation. -/
theorem EffectiveCosts.cold (costs : EffectiveCosts) :
    (costs.prices ⟨1,1,1,0,0⟩).choose 1 = .fresh := by
  apply TemplateCosts.cold
  simp only [prices, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  omega

/-- Hoisting/configuring the strategy has a separate charge; choosing reuse does
not erase that fee from a complete publication bound. -/
theorem EffectiveCosts.configuration_covered (costs : EffectiveCosts) (budget : EffectiveBudget)
    (fee base : Nat) (paid : fee ≤ (costs.prices budget).freshTotal budget.calls -
      (costs.prices budget).selectedTotal budget.calls) :
    base + fee + (costs.prices budget).selectedTotal budget.calls ≤
      base + (costs.prices budget).freshTotal budget.calls :=
  (costs.prices budget).configuration_covered budget.calls fee base paid

/-- Full publication may construct different native carriers (qualified wrapper
versus nested invoker), so its fresh/prepared bases need not be equal. Include
actual strategy-specific construction, binding and admission costs explicitly. -/
def EffectiveCosts.chooseWorkflow (costs : EffectiveCosts) (budget : EffectiveBudget)
    (freshBase preparedBase : Nat) : CheckMode :=
  if preparedBase + (costs.prices budget).sharedTotal budget.calls <
      freshBase + (costs.prices budget).freshTotal budget.calls then .shared else .fresh

/-- Complete selected workflow cost, including the separately supplied bases.
The selection/configuration fee must be added independently at its actual horizon. -/
def EffectiveCosts.selectedWorkflow (costs : EffectiveCosts) (budget : EffectiveBudget)
    (freshBase preparedBase : Nat) : Nat :=
  match costs.chooseWorkflow budget freshBase preparedBase with
  | .fresh => freshBase + (costs.prices budget).freshTotal budget.calls
  | .shared => preparedBase + (costs.prices budget).sharedTotal budget.calls

/-- Unequal carrier-construction/binding/approval work cannot disappear through
cancellation of a supposedly common base. Ties keep the ordinary reference. -/
theorem EffectiveCosts.selected_workflow_bound (costs : EffectiveCosts) (budget : EffectiveBudget)
    (freshBase preparedBase : Nat) :
    costs.selectedWorkflow budget freshBase preparedBase ≤
      freshBase + (costs.prices budget).freshTotal budget.calls := by
  by_cases cheap : preparedBase + (costs.prices budget).sharedTotal budget.calls <
      freshBase + (costs.prices budget).freshTotal budget.calls
  · simpa [selectedWorkflow, chooseWorkflow, cheap] using Nat.le_of_lt cheap
  · simp [selectedWorkflow, chooseWorkflow, cheap]

/-- One unconditional cache layer during joint construction/admission. Probes
that discard successors and real first entries each repeat cold work without
explicit preparation. invocations includes probes AND real calls; no body or
contract validation is removed. Unguarded declared shapes are counted up front,
including unused shapes. Guarded preparation falls back by prepareShape_guarded. -/
structure ShapePreparationBudget where
  declaredShapes : Nat
  discardedMisses : Nat
  entryMisses : Nat
  invocations : Nat
  extraCollections : Nat
  deriving Repr

/-- Actual repeated cold resolution/assembly/cache-owner construction events.
These counts are supplied for the chosen workflow, not inferred from old timing. -/
def ShapePreparationBudget.runtimeEvents (budget : ShapePreparationBudget) :=
  budget.discardedMisses + budget.entryMisses

/-- Reuse primitive effective-method prices; allocation includes cache-owner work
at that layer. Child and outer layers may use different prices, summed by callers. -/
def EffectiveCosts.preparationEvent (costs : EffectiveCosts) := costs.resolve + costs.prepare + costs.allocation

/-- Current argument checks, method effects, contract validation and publication
remain in the appropriate supplied base; every invocation still pays its dispatch,
invocation and transport work. This does not predict native collector behavior. -/
def ShapePreparationBudget.runtimeTotal (budget : ShapePreparationBudget) (costs : EffectiveCosts) (base : Nat) :=
  base + budget.runtimeEvents * costs.preparationEvent +
    budget.invocations * (costs.hit + costs.invoke + costs.transport)

/-- Charge declaration/configuration, all prepared cache entries, and explicitly
budgeted excess GC. Prepared/fresh carrier construction bases need not be equal. -/
def ShapePreparationBudget.declaredTotal (budget : ShapePreparationBudget) (costs : EffectiveCosts)
    (base setup : Nat) :=
  base + setup + budget.declaredShapes * costs.preparationEvent +
    budget.extraCollections * costs.collectionPrice +
    budget.invocations * (costs.hit + costs.invoke + costs.transport)

/-- A real operation saving must cover construction differences, configuration
AND excess-GC work before declaration-time preparation is justified. -/
theorem ShapePreparationBudget.preparation_covered (budget : ShapePreparationBudget) (costs : EffectiveCosts)
    (runtimeBase preparedBase setup : Nat) (supported : budget.declaredShapes ≤ budget.runtimeEvents)
    (paid : preparedBase + setup + budget.extraCollections * costs.collectionPrice ≤
      runtimeBase + (budget.runtimeEvents - budget.declaredShapes) * costs.preparationEvent) :
    budget.declaredTotal costs preparedBase setup ≤ budget.runtimeTotal costs runtimeBase := by
  have events : (budget.runtimeEvents - budget.declaredShapes) * costs.preparationEvent +
      budget.declaredShapes * costs.preparationEvent = budget.runtimeEvents * costs.preparationEvent := by
    rw [← Nat.add_mul, Nat.sub_add_cancel supported]
  unfold declaredTotal runtimeTotal
  omega

/-- Choose the explicit preparation mode only when its COMPLETE supplied budget
is smaller. Ties and unpaid cold/GC cases keep ordinary invocation-time preparation. -/
def ShapePreparationBudget.choose (budget : ShapePreparationBudget) (costs : EffectiveCosts)
    (runtimeBase preparedBase setup : Nat) : CheckMode :=
  if budget.declaredTotal costs preparedBase setup < budget.runtimeTotal costs runtimeBase then .shared else .fresh

/-- Full selected operation budget; this is not a wall-clock selector or an
embedded empirical frequency. Native models expose the choice explicitly. -/
def ShapePreparationBudget.selectedTotal (budget : ShapePreparationBudget) (costs : EffectiveCosts)
    (runtimeBase preparedBase setup : Nat) :=
  match budget.choose costs runtimeBase preparedBase setup with
  | .shared => budget.declaredTotal costs preparedBase setup
  | .fresh => budget.runtimeTotal costs runtimeBase

/-- The supplied choice cannot exceed the unprepared reference budget, including
cold declarations, owner construction, unequal bases and excess collections. -/
theorem ShapePreparationBudget.selected_bound (budget : ShapePreparationBudget) (costs : EffectiveCosts)
    (runtimeBase preparedBase setup : Nat) :
    budget.selectedTotal costs runtimeBase preparedBase setup ≤ budget.runtimeTotal costs runtimeBase := by
  by_cases cheap : budget.declaredTotal costs preparedBase setup < budget.runtimeTotal costs runtimeBase
  · simpa [selectedTotal, choose, cheap] using Nat.le_of_lt cheap
  · simp [selectedTotal, choose, cheap]

/-- Sharing one context-independent definition amortizes construction over changed
views, but every probe/call adds current-view argument validation and representation
work. All those invocations, plus excess GC, must be included in the horizon. -/
structure ContextPreparationBudget where
  revisions : Nat
  invocations : Nat
  extraCollections : Nat
  deriving Repr

/-- Reuse TemplateCosts rather than introduce another runtime selector. setup
includes first definition/negative-check/preparation/model binding; specialize is
per-view outer binding, rebuild is per-view captured child reconstruction. The
explicit context argument's extra Type/representation work is NOT free. -/
def ContextPreparationBudget.prices (budget : ContextPreparationBudget) (costs : TemplateCosts)
    (contextArgument collectionPrice : Nat) : TemplateCosts :=
  { costs with setup := costs.setup + budget.invocations * contextArgument + budget.extraCollections * collectionPrice }

/-- The shared-definition choice charges cold construction, every current-view
argument, per-view binding and supplied GC. Common body/contract/admission work
stays in base only when actually equal for the two representations. -/
theorem ContextPreparationBudget.selected_bound (budget : ContextPreparationBudget) (costs : TemplateCosts)
    (contextArgument collectionPrice base : Nat) :
    base + (budget.prices costs contextArgument collectionPrice).selectedTotal budget.revisions ≤
      base + costs.freshTotal budget.revisions :=
  Nat.add_le_add_left ((budget.prices costs contextArgument collectionPrice).selected_bound budget.revisions) base

/-- An explicit amortization condition covers the additional argument and excess
collector work before concluding a sharing bound. These prices/counts are supplied,
not imported from Lean output or inferred from a favorable native sample. -/
theorem ContextPreparationBudget.sharing_covered (budget : ContextPreparationBudget) (costs : TemplateCosts)
    (contextArgument collectionPrice : Nat) (cheaper : costs.specialize ≤ costs.rebuild)
    (paid : costs.setup + budget.invocations * contextArgument + budget.extraCollections * collectionPrice ≤
      budget.revisions * (costs.rebuild - costs.specialize)) :
    (budget.prices costs contextArgument collectionPrice).sharedTotal budget.revisions ≤
      costs.freshTotal budget.revisions :=
  template_amortized (budget.prices costs contextArgument collectionPrice) budget.revisions cheaper paid

/-- Count actual factory creations, calls and Simula callbacks. A reused wrapper
skeleton is still charged once, including the very first factory in a process. -/
structure SimulaFactoryBudget where
  factories : Nat
  invocations : Nat
  methods : Nat
  extraCollections : Nat
  deriving Repr

/-- Supplied operation prices: common child definition/check work; reference
binding plus traversal setup; shared wrapper setup/binding; compiled per-method
closures; and complete per-call traversal/compiled costs. GC is an extra price.
No measured times or assumed zero-cost argument validation are embedded here. -/
structure SimulaFactoryCosts where
  wrapperSetup : Nat
  rebuild : Nat
  bind : Nat
  child : Nat
  chain : Nat
  traversal : Nat
  invoke : Nat
  collection : Nat
  deriving Repr

/-- Reference factories reconstruct their wrappers; all current calls execute. -/
def SimulaFactoryBudget.referenceTotal (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts) : Nat :=
  budget.factories * (costs.child + costs.rebuild) + budget.invocations * costs.traversal

/-- Complete compiled budget includes once-only wrapper preparation, every fresh
child and binding, every callback closure, current calls and supplied excess GC. -/
def SimulaFactoryBudget.compiledTotal (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts) : Nat :=
  costs.wrapperSetup + budget.factories * (costs.child + costs.bind + budget.methods * costs.chain) +
    budget.invocations * costs.invoke + budget.extraCollections * costs.collection

/-- Strictly cheaper complete budgets select compilation; ties keep reference. -/
def SimulaFactoryBudget.choose (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts) : CheckMode :=
  if budget.compiledTotal costs < budget.referenceTotal costs then .shared else .fresh

/-- Charge the selected factory/call representation including its cold setup. -/
def SimulaFactoryBudget.selectedTotal (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts) : Nat :=
  match budget.choose costs with
  | .fresh => budget.referenceTotal costs
  | .shared => budget.compiledTotal costs

/-- Conditional total-work bound retains cold and call-heavy fallback without
assuming callback compilation, current checks or shared setup are free. -/
theorem SimulaFactoryBudget.selected_bound (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts) (base : Nat) :
    base + budget.selectedTotal costs ≤ base + budget.referenceTotal costs := by
  by_cases cheap : budget.compiledTotal costs < budget.referenceTotal costs
  · simpa [selectedTotal, choose, cheap] using Nat.add_le_add_left (Nat.le_of_lt cheap) base
  · simp [selectedTotal, choose, cheap]

/-- Paying the shared wrapper/callback setup is a necessary admission condition
before asserting this compiled budget is no larger than the complete reference. -/
theorem SimulaFactoryBudget.compilation_covered (budget : SimulaFactoryBudget) (costs : SimulaFactoryCosts)
    (paid : costs.wrapperSetup + budget.factories * (costs.bind + budget.methods * costs.chain) +
      budget.invocations * costs.invoke + budget.extraCollections * costs.collection ≤
      budget.factories * costs.rebuild + budget.invocations * costs.traversal) :
    budget.compiledTotal costs ≤ budget.referenceTotal costs := by
  simp only [compiledTotal, referenceTotal, Nat.mul_add] at *
  omega

/-- Compose a captured-view cold phase with a later checked shared-definition
handoff. Base includes its real initial calls; setup includes all first owner
handoff rebuild/check work. The workflow wrapper's extra construction is admitted
only when the later selected saving covers it; it is never silently free. -/
theorem ContextPreparationBudget.staged_bound (budget : ContextPreparationBudget) (costs : TemplateCosts)
    (contextArgument collectionPrice workflowBinding base : Nat)
    (paid : workflowBinding ≤ (budget.prices costs contextArgument collectionPrice).freshTotal budget.revisions -
      (budget.prices costs contextArgument collectionPrice).selectedTotal budget.revisions) :
    base + workflowBinding + (budget.prices costs contextArgument collectionPrice).selectedTotal budget.revisions ≤
      base + costs.freshTotal budget.revisions :=
  (budget.prices costs contextArgument collectionPrice).configuration_covered budget.revisions workflowBinding base paid

/-- Actual context reconstructions, post-handoff invocations and excess GC.
Binding is paid on every changed view, never presumed free from earlier calls. -/
structure SimulaBindingBudget where
  reconstructions : Nat
  invocations : Nat
  extraCollections : Nat
  deriving Repr

/-- Supplied full setup, per-view binding and per-call prices for shared-row and
bound-view representations. Call prices include actual Type/representation work;
table bytes and primitive prices are empirical inputs, not Lean runtime claims. -/
structure SimulaBindingCosts where
  sharedSetup : Nat
  boundSetup : Nat
  bind : Nat
  sharedCall : Nat
  boundCall : Nat
  collection : Nat
  deriving Repr

/-- Shared code still validates/transmits current context on every invocation. -/
def SimulaBindingBudget.sharedTotal (budget : SimulaBindingBudget) (costs : SimulaBindingCosts) : Nat :=
  costs.sharedSetup + budget.invocations * costs.sharedCall

/-- Bound code validates/binds each reconstructed view once, then still executes
all current units/body/contract checks. Supplied extra collector work is charged. -/
def SimulaBindingBudget.boundTotal (budget : SimulaBindingBudget) (costs : SimulaBindingCosts) : Nat :=
  costs.boundSetup + budget.reconstructions * costs.bind + budget.invocations * costs.boundCall +
    budget.extraCollections * costs.collection

/-- Select only a strictly cheaper complete operation budget; ties keep shared. -/
def SimulaBindingBudget.choose (budget : SimulaBindingBudget) (costs : SimulaBindingCosts) : CheckMode :=
  if budget.boundTotal costs < budget.sharedTotal costs then .shared else .fresh

/-- Selected total includes setup and reconstruction, not only a hot-call saving. -/
def SimulaBindingBudget.selectedTotal (budget : SimulaBindingBudget) (costs : SimulaBindingCosts) : Nat :=
  match budget.choose costs with
  | .shared => budget.boundTotal costs
  | .fresh => budget.sharedTotal costs

/-- A conditional selection bound does not assert the native cost inputs or GC. -/
theorem SimulaBindingBudget.selected_bound (budget : SimulaBindingBudget) (costs : SimulaBindingCosts) (base : Nat) :
    base + budget.selectedTotal costs ≤ base + budget.sharedTotal costs := by
  by_cases cheap : budget.boundTotal costs < budget.sharedTotal costs
  · simpa [selectedTotal, choose, cheap] using Nat.add_le_add_left (Nat.le_of_lt cheap) base
  · simp [selectedTotal, choose, cheap]

/-- Actual per-call saving must pay every new binding and all extra setup/GC.
For revision-heavy or short horizons this condition can fail. -/
theorem SimulaBindingBudget.binding_covered (budget : SimulaBindingBudget) (costs : SimulaBindingCosts)
    (cheaper : costs.boundCall ≤ costs.sharedCall)
    (paid : costs.boundSetup + budget.reconstructions * costs.bind + budget.extraCollections * costs.collection ≤
      costs.sharedSetup + budget.invocations * (costs.sharedCall - costs.boundCall)) :
    budget.boundTotal costs ≤ budget.sharedTotal costs := by
  have restore : budget.invocations * (costs.sharedCall - costs.boundCall) +
      budget.invocations * costs.boundCall = budget.invocations * costs.sharedCall := by
    rw [← Nat.mul_add, Nat.sub_add_cancel cheaper]
  simp only [boundTotal, sharedTotal]
  omega

/-- Keyed-table sizing is an independent representation choice. Only supplied
lower allocation/work prices justify adding its saving to the binding bound;
all owner rebuild, negative and approval work remains explicit common base. -/
theorem SimulaBindingBudget.tables_covered (budget : SimulaBindingBudget) (costs : SimulaBindingCosts)
    (tables defaultPrice sizedPrice base : Nat) (sized : sizedPrice ≤ defaultPrice)
    (binding : budget.boundTotal costs ≤ budget.sharedTotal costs) :
    base + tables * sizedPrice + budget.boundTotal costs ≤
      base + tables * defaultPrice + budget.sharedTotal costs :=
  Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left tables sized) base) binding

end PreparationCosts

end LeanPoo.Functional.ContractFamily

namespace LeanPoo.Functional.ContractFamily.PreparationCosts
/-- Supplied storage preparation prices separate constructor dispatch, temporary
staging and pruning from the binding/approval work common to both strategies. -/
structure EmptyStorageCosts where
  keyword : Nat
  emptyFactory : Nat
  staging : Nat
  pruning : Nat
  interfaceSetup : Nat
  collection : Nat
  deriving Repr
/-- Select same-kind empty storage only when all removed preparation work pays
its one-time interface setup AND supplied excess GC over the complete horizon.
The common base still includes current construction, binding and joint approval. -/
theorem EmptyStorageCosts.covered (costs : EmptyStorageCosts) (tables collections base : Nat)
    (paid : costs.interfaceSetup + tables * costs.emptyFactory + collections * costs.collection ≤
      tables * costs.keyword + costs.staging + costs.pruning) :
    base + costs.interfaceSetup + tables * costs.emptyFactory + collections * costs.collection ≤
      base + tables * costs.keyword + costs.staging + costs.pruning := by omega
end LeanPoo.Functional.ContractFamily.PreparationCosts


namespace LeanPoo.Functional.ContractFamily.PreparationCosts
/-- Supplied recursive source costs distinguish memo lookup/hits, cold machine
steps, private storage preparation and CURRENT boundary validation. -/
structure RecursiveMemoCosts where
  fresh : Nat
  hit : Nat
  setup : Nat
  admission : Nat
  collection : Nat
  deriving Repr
/-- Raw memo savings justify reuse only if they cover setup and excess GC over
all calls. The same current-input/output admission cost is charged on BOTH sides;
no result cache permits dropping Type or catalog checks. -/
theorem RecursiveMemoCosts.covered (costs : RecursiveMemoCosts) (calls extraCollections base : Nat)
    (paid : costs.setup + calls * costs.hit + extraCollections * costs.collection ≤ calls * costs.fresh) :
    base + calls * costs.admission + costs.setup + calls * costs.hit + extraCollections * costs.collection ≤
      base + calls * costs.admission + calls * costs.fresh := by omega
end LeanPoo.Functional.ContractFamily.PreparationCosts

