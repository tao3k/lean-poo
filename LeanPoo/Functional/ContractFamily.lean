import LeanPoo.Functional.DeclarativeMetadata
import Std.Data.DHashMap.Lemmas

/-! Projected contract construction and late-bound wrapper retention.
This advances generalized-prototype future work, with explicit pure sources. -/
namespace LeanPoo.Functional.ContractFamily
open DeclarativeMetadata

/-- Invoke a descriptor against the caller-supplied current state and arguments.
Contract failures remain in Except; success returns only the checked result/state.
The wrapper closes over the executor and descriptor, never a previous snapshot. -/
def bind (contract : Contract Atom Args Result)
    (execute : State → Args → Except Error (Result × State)) (current : State) (args : Args) :=
  (contract.invoke (execute current) args).map fun receipt => (receipt.result,receipt.state)

/-- The binding has exactly the same observations as invoking the contract on current state. -/
theorem bind_current (contract : Contract Atom Args Result)
    (execute : State → Args → Except Error (Result × State)) (current : State) (args : Args) :
    bind contract execute current args =
      (contract.invoke (execute current) args).map (fun receipt => (receipt.result,receipt.state)) := rfl

/-- Pure contract-construction protocol. Each key has a closed Context; project
extracts it from policy/cooked data and construct may return a typed build error.
Descriptor reuse is justified by equality of this input under the same source. -/
structure Source (Key Policy Cooked : Type) (Atom Args Result : Key → Type) (BuildError : Type) where
  Context : Key → Type
  keys : Policy → Cooked → List Key
  project : (key : Key) → Policy → Cooked → Context key
  construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key))

variable {Key Policy Cooked BuildError Error State : Type} {Atom Args Result : Key → Type}
variable (source : Source Key Policy Cooked Atom Args Result BuildError)
variable (execute : (key : Key) → State → Args key → Except Error (Result key × State))
variable (policy : Policy) (cooked : Cooked)

/-- A per-key descriptor with its construction equation and a late-bound wrapper.
The dependent policy/cooked indices record which projected input justifies reuse. -/
structure Cell (key : Key) where
  contract : Contract (Atom key) (Args key) (Result key)
  origin : source.construct key (source.project key policy cooked) = .ok contract
  bound : State → Args key → Except (Failure Error) (Result key × State)
  binding : bound = bind contract (execute key)

variable {source execute policy cooked}
variable {oldExecute : (key : Key) → State → Args key → Except Error (Result key × State)}
variable {oldPolicy : Policy} {oldCooked : Cooked} {key : Key}

/-- Transport a cell to the new policy/cooked indices using equal projected inputs
and equal executors. Returns the original descriptor and wrapper without construct/bind. -/
def Cell.retain (old : Cell source oldExecute oldPolicy oldCooked key)
    (same : source.project key oldPolicy oldCooked = source.project key policy cooked)
    (entry : oldExecute = execute) : Cell source execute policy cooked key where
  contract := old.contract
  origin := by rw [← same]; exact old.origin
  bound := old.bound
  binding := old.binding.trans (congrArg (fun runner => bind old.contract (runner key)) entry)

/-- Reuse the descriptor under equal projected inputs, but bind the new executor.
No construction runs; the new wrapper still consumes its invocation-time state. -/
def Cell.rebind (old : Cell source oldExecute oldPolicy oldCooked key)
    (same : source.project key oldPolicy oldCooked = source.project key policy cooked) :
    Cell source execute policy cooked key where
  contract := old.contract
  origin := by rw [← same]; exact old.origin
  bound := bind old.contract (execute key)
  binding := rfl

/-- Retaining a valid cell preserves the descriptor value exactly. -/
theorem Cell.retain_contract (old : Cell source oldExecute oldPolicy oldCooked key) (same entry) :
    (old.retain (execute := execute) (policy := policy) (cooked := cooked) same entry).contract = old.contract := rfl

/-- With equal executors, retaining a cell preserves its wrapper exactly. -/
theorem Cell.retain_bound (old : Cell source oldExecute oldPolicy oldCooked key) (same entry) :
    (old.retain (execute := execute) (policy := policy) (cooked := cooked) same entry).bound = old.bound := rfl

/-- Changing only the executor keeps the same descriptor while permitting rebinding. -/
theorem Cell.rebind_contract (old : Cell source oldExecute oldPolicy oldCooked key) (same) :
    (old.rebind (execute := execute) (policy := policy) (cooked := cooked) same).contract = old.contract := rfl

variable [BEq Key] [LawfulBEq Key] [Hashable Key]

/-- A dependent key-indexed collection plus ordered construction/binding/reuse traces.
Traces describe actual selected branches, not estimated elapsed time. -/
structure Family (source : Source Key Policy Cooked Atom Args Result BuildError)
    (execute : (key : Key) → State → Args key → Except Error (Result key × State)) (policy : Policy) (cooked : Cooked) where
  cells : Std.DHashMap Key (Cell source execute policy cooked)
  built : List Key
  bound : List Key
  reused : List Key

/-- Typed preparation refusal: duplicate support, missing service or constructor error.
A caller must not publish a partial family after any of these errors. -/
inductive PreparationError (Key BuildError : Type) where
  | duplicate (key : Key)
  | missing (key : Key)
  | construction (key : Key) (error : BuildError)
  deriving Repr

variable (source execute policy cooked)

/-- Stage one key into a private family. Reject duplicates and missing services first.
Equal closed inputs reuse descriptors; equal executors additionally reuse wrappers.
Fresh construction failures return PreparationError without a completed family. -/
def Family.step [∀ key, DecidableEq (source.Context key)]
    (old : Option (Family source oldExecute oldPolicy oldCooked)) (entry : Option (PLift (oldExecute = execute)))
    (prior : Family source execute policy cooked) (available : Key → Bool) (key : Key) :
    Except (PreparationError Key BuildError) (Family source execute policy cooked) :=
  if (prior.cells.get? key).isSome then .error (.duplicate key) else
  if !available key then .error (.missing key) else
  -- Install one validated cell and record the actual construction/binding branches.
  let install (cell : Cell source execute policy cooked key) (built bound : Bool) :=
    { prior with cells := prior.cells.insert key cell
                 built := if built then prior.built ++ [key] else prior.built
                 bound := if bound then prior.bound ++ [key] else prior.bound
                 reused := if built then prior.reused else prior.reused ++ [key] }
  match old.bind (fun family => family.cells.get? key) with
  | some cached =>
    if same : source.project key oldPolicy oldCooked = source.project key policy cooked then
      match entry with
      | some equal => .ok (install (cached.retain same equal.down) false false)
      | none => .ok (install (cached.rebind same) false true)
    else fresh install
  | none => fresh install
where
  -- Translate a constructor failure with its key; bind only successful descriptors.
  fresh (install : Cell source execute policy cooked key → Bool → Bool → Family source execute policy cooked) :=
    match compiled : source.construct key (source.project key policy cooked) with
    | .error error => .error (.construction key error)
    | .ok contract => .ok (install ⟨contract,compiled,bind contract (execute key),rfl⟩ true true)

/-- Build the requested support in source order, optionally reusing an old family.
Stops at the first duplicate/missing/build error; success contains only current keys.
The immutable old family is available unchanged to the publication caller. -/
def refresh [∀ key, DecidableEq (source.Context key)]
    (old : Option (Family source oldExecute oldPolicy oldCooked)) (entry : Option (PLift (oldExecute = execute)))
    (available : Key → Bool) : Except (PreparationError Key BuildError) (Family source execute policy cooked) :=
  -- Fold in support order; stop on the first error without exposing a partial family.
  let rec go (prior : Family source execute policy cooked) : List Key → Except (PreparationError Key BuildError) (Family source execute policy cooked)
    | [] => .ok prior
    | key :: rest => match prior.step source execute policy cooked old entry available key with
      | .error error => .error error
      | .ok next => go next rest
  go ⟨{},[],[],[]⟩ (source.keys policy cooked)

/-- Exact source-level work accounting for a retained descriptor and binding.
Neither construct nor bind executes in this branch. -/
theorem Family.step_retained [∀ key, DecidableEq (source.Context key)]
    (old : Family source oldExecute oldPolicy oldCooked) (entry : oldExecute = execute)
    (prior : Family source execute policy cooked) (available : Key → Bool) (key : Key)
    (cached : Cell source oldExecute oldPolicy oldCooked key)
    (pending : prior.cells.get? key = none) (found : old.cells.get? key = some cached)
    (present : available key = true)
    (same : source.project key oldPolicy oldCooked = source.project key policy cooked) :
    (prior.step source execute policy cooked (some old) (some ⟨entry⟩) available key).map
      (fun next => (next.built,next.bound,next.reused)) =
      .ok (prior.built,prior.bound,prior.reused ++ [key]) := by
  simp [Family.step, pending, found, present, same, Except.map]

/-- Cold family construction: refresh with no prior descriptors or wrappers.
Checks availability and propagates the same typed preparation failures as refresh. -/
def prepare [∀ key, DecidableEq (source.Context key)] (available : Key → Bool) :=
  refresh source execute policy cooked (oldExecute := execute) (oldPolicy := policy) (oldCooked := cooked)
    none (some ⟨rfl⟩) available

/-- Even a retained descriptor is refused if its service disappeared. -/
theorem Family.step_missing [∀ key, DecidableEq (source.Context key)]
    (old : Option (Family source oldExecute oldPolicy oldCooked)) (entry)
    (prior : Family source execute policy cooked) (available : Key → Bool) (key : Key)
    (pending : prior.cells.get? key = none) (missing : available key = false) :
    prior.step source execute policy cooked old entry available key = .error (.missing key) := by
  simp only [Family.step, pending, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, missing, Bool.not_false, ↓reduceIte]

/-- The policy, cooked representation and certified family published together.
Keeping the old value on refusal preserves their mutual correspondence. -/
structure Snapshot where
  policy : Policy
  cooked : Cooked
  family : Family source execute policy cooked

/-- Refresh and approve a candidate at one immutable boundary. Returns the typed
preparation/admission outcome and either the complete new snapshot or exact old one.
No partially constructed or rejected candidate becomes the published snapshot. -/
def publish [∀ key, DecidableEq (source.Context key)] (old : Snapshot source execute)
    (policy : Policy) (cooked : Cooked) (available : Key → Bool)
    (admit : Family source execute policy cooked → Except AdmissionError Unit) :=
  let outcome : Except (Sum (PreparationError Key BuildError) AdmissionError) (Family source execute policy cooked) := do
    let family ← (refresh source execute policy cooked (some old.family) (some ⟨rfl⟩) available).mapError Sum.inl
    let _ ← (admit family).mapError Sum.inr
    return family
  (outcome,match outcome with | .error _ => old | .ok family => ⟨policy,cooked,family⟩)

/-- Any preparation or application refusal returns the original snapshot exactly. -/
theorem publish_refused [∀ key, DecidableEq (source.Context key)] (old : Snapshot source execute)
    (policy : Policy) (cooked : Cooked) (available : Key → Bool)
    (admit : Family source execute policy cooked → Except AdmissionError Unit)
    (error : Sum (PreparationError Key BuildError) AdmissionError)
    (refused : (publish source execute old policy cooked available admit).1 = .error error) :
    (publish source execute old policy cooked available admit).2 = old := by
  simp only [publish] at refused ⊢
  rw [refused]


/-- Closed shared preparation, followed by heterogeneous per-key projections.
The expensive prepare function cannot observe the ambient policy or snapshot. -/
structure SharedProjection (Key Policy Cooked Shared Prepared : Type) (Context : Key → Type) where
  input : Policy → Cooked → Shared
  prepare : Shared → Prepared
  project : (key : Key) → Prepared → Context key

namespace SharedProjection
omit [BEq Key] [LawfulBEq Key] [Hashable Key]
variable {Shared Prepared : Type} {Context : Key → Type}
variable (projection : SharedProjection Key Policy Cooked Shared Prepared Context)

/-- A prepared shared value certified to equal preparation of the indexed closed input.
It contains no ambient policy, service executor or invocation-time snapshot. -/
structure Cache (input : Shared) where
  value : Prepared
  origin : value = projection.prepare input

/-- Reuse a certified prepared value only when its closed shared input is equal.
Returns the prepared cache plus zero/one calls to projection.prepare; misses rebuild.
This count omits equality, allocation and runtime costs, which need separate prices. -/
def refresh [DecidableEq Shared] (input : Shared)
    (old : Option (Σ prior, Cache projection prior)) : Cache projection input × Nat :=
  match old with
  | some ⟨prior, cached⟩ =>
    if same : prior = input then (⟨cached.value, by simpa [same] using cached.origin⟩, 0)
    else (⟨projection.prepare input, rfl⟩, 1)
  | none => (⟨projection.prepare input, rfl⟩, 1)

/-- Every cached heterogeneous input equals fresh closed preparation. -/
theorem refresh_project [DecidableEq Shared] (input : Shared)
    (old : Option (Σ prior, Cache projection prior)) (key : Key) :
    projection.project key (refresh projection input old).1.value =
      projection.project key (projection.prepare input) :=
  congrArg (projection.project key) (refresh projection input old).1.origin

/-- Same-context revision retains the actual prepared value and invokes no prepare. -/
theorem refresh_retained [DecidableEq Shared] (input : Shared) (old : Cache projection input) :
    (refresh projection input (some ⟨input,old⟩)).1.value = old.value ∧
    (refresh projection input (some ⟨input,old⟩)).2 = 0 := by
  simp [refresh]

/-- Preparation is bounded independently of the number of heterogeneous contracts.
This counts calls to prepare, not wall time, allocation or Scheme execution. -/
theorem refresh_cost [DecidableEq Shared] (input : Shared)
    (old : Option (Σ prior, Cache projection prior)) :
    (refresh projection input old).2 ≤ 1 := by
  cases old with
  | none => simp [refresh]
  | some cached => rcases cached with ⟨prior,cached⟩; simp only [refresh]; split <;> simp

/-- Adapt closed shared preparation to the existing contract-source protocol.
Keys and constructor errors are unchanged; this reference definition prepares afresh
per projection. refresh_project justifies the separately cached native lookup. -/
def toSource (keys : Policy → Cooked → List Key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key))) :
    Source Key Policy Cooked Atom Args Result BuildError where
  Context := Context
  keys := keys
  project := fun key policy cooked => projection.project key (projection.prepare (projection.input policy cooked))
  construct := construct

/-- The native cached lookup is an implementation of the existing source projection,
so contract construction, binding and publication laws apply without weaker inputs. -/
theorem cached_source_project [DecidableEq Shared] (keys : Policy → Cooked → List Key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key)))
    (policy : Policy) (cooked : Cooked) (old : Option (Σ prior, Cache projection prior)) (key : Key) :
    projection.project key (refresh projection (projection.input policy cooked) old).1.value =
      (toSource projection keys construct).project key policy cooked :=
  refresh_project projection (projection.input policy cooked) old key

/-- Equal closed shared inputs imply equal projected per-key contexts. -/
theorem same_context (oldPolicy policy : Policy) (oldCooked cooked : Cooked)
    (same : projection.input oldPolicy oldCooked = projection.input policy cooked) (key : Key) :
    projection.project key (projection.prepare (projection.input oldPolicy oldCooked)) =
    projection.project key (projection.prepare (projection.input policy cooked)) := by rw [same]

/-- A changed shared context can still leave a specific contract input unchanged;
Cell.retain then preserves both its descriptor and late-bound invocation wrapper. -/
theorem retain_origin (keys : Policy → Cooked → List Key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key)))
    (old : Cell (toSource projection keys construct) execute oldPolicy oldCooked key)
    (same : projection.project key (projection.prepare (projection.input oldPolicy oldCooked)) =
      projection.project key (projection.prepare (projection.input policy cooked))) :
    construct key (projection.project key (projection.prepare (projection.input policy cooked))) = .ok old.contract := by
  rw [← same]
  exact old.origin
/-- Adapt a direct per-key projection with the original support/constructor protocol.
This constructor alone does not assert coherence: direct_source_project/eq require
an explicit equation with the reference shared preparation for every key/input. -/
def directSource (keys : Policy → Cooked → List Key)
    (direct : (key : Key) → Shared → Context key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key))) :
    Source Key Policy Cooked Atom Args Result BuildError where
  Context := Context
  keys := keys
  project := fun key policy cooked => direct key (projection.input policy cooked)
  construct := construct

/-- A supplied per-key coherence equation makes direct and prepared projections equal. -/
theorem direct_source_project (keys : Policy → Cooked → List Key)
    (direct : (key : Key) → Shared → Context key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key)))
    (coherent : ∀ key input, direct key input = projection.project key (projection.prepare input))
    (key : Key) (policy : Policy) (cooked : Cooked) :
    (projection.directSource keys direct construct).project key policy cooked =
      (projection.toSource keys construct).project key policy cooked := coherent key _

/-- Equal projection implementations give exactly the same source semantics,
including construction errors and all downstream contract/binding laws. -/
theorem direct_source_eq (keys : Policy → Cooked → List Key)
    (direct : (key : Key) → Shared → Context key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key)))
    (coherent : ∀ key input, direct key input = projection.project key (projection.prepare input)) :
    projection.directSource keys direct construct = projection.toSource keys construct := by
  unfold directSource toSource
  congr 1
  funext key policy cooked
  exact coherent key _

end SharedProjection

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

end PreparationCosts

end LeanPoo.Functional.ContractFamily
