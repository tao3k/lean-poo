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

end LeanPoo.Functional.ContractFamily
