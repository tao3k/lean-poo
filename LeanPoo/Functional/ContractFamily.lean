import LeanPoo.Functional.DeclarativeMetadata
import Std.Data.DHashMap.Lemmas

/-! Projected contract construction and late-bound wrapper retention.
This advances generalized-prototype future work, with explicit pure sources. -/
namespace LeanPoo.Functional.ContractFamily
open DeclarativeMetadata

/-- A bound wrapper receives the actual current snapshot at every call. -/
def bind (contract : Contract Atom Args Result)
    (execute : State → Args → Except Error (Result × State)) (current : State) (args : Args) :=
  (contract.invoke (execute current) args).map fun receipt => (receipt.result,receipt.state)

theorem bind_current (contract : Contract Atom Args Result)
    (execute : State → Args → Except Error (Result × State)) (current : State) (args : Args) :
    bind contract execute current args =
      (contract.invoke (execute current) args).map (fun receipt => (receipt.result,receipt.state)) := rfl

structure Source (Key Policy Cooked : Type) (Atom Args Result : Key → Type) (BuildError : Type) where
  Context : Key → Type
  keys : Policy → Cooked → List Key
  project : (key : Key) → Policy → Cooked → Context key
  construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key))

variable {Key Policy Cooked BuildError Error State : Type} {Atom Args Result : Key → Type}
variable (source : Source Key Policy Cooked Atom Args Result BuildError)
variable (execute : (key : Key) → State → Args key → Except Error (Result key × State))
variable (policy : Policy) (cooked : Cooked)

structure Cell (key : Key) where
  contract : Contract (Atom key) (Args key) (Result key)
  origin : source.construct key (source.project key policy cooked) = .ok contract
  bound : State → Args key → Except (Failure Error) (Result key × State)
  binding : bound = bind contract (execute key)

variable {source execute policy cooked}
variable {oldExecute : (key : Key) → State → Args key → Except Error (Result key × State)}
variable {oldPolicy : Policy} {oldCooked : Cooked} {key : Key}

def Cell.retain (old : Cell source oldExecute oldPolicy oldCooked key)
    (same : source.project key oldPolicy oldCooked = source.project key policy cooked)
    (entry : oldExecute = execute) : Cell source execute policy cooked key where
  contract := old.contract
  origin := by rw [← same]; exact old.origin
  bound := old.bound
  binding := old.binding.trans (congrArg (fun runner => bind old.contract (runner key)) entry)

/-- Changing the executor retains the descriptor but binds a new wrapper. -/
def Cell.rebind (old : Cell source oldExecute oldPolicy oldCooked key)
    (same : source.project key oldPolicy oldCooked = source.project key policy cooked) :
    Cell source execute policy cooked key where
  contract := old.contract
  origin := by rw [← same]; exact old.origin
  bound := bind old.contract (execute key)
  binding := rfl

theorem Cell.retain_contract (old : Cell source oldExecute oldPolicy oldCooked key) (same entry) :
    (old.retain (execute := execute) (policy := policy) (cooked := cooked) same entry).contract = old.contract := rfl

theorem Cell.retain_bound (old : Cell source oldExecute oldPolicy oldCooked key) (same entry) :
    (old.retain (execute := execute) (policy := policy) (cooked := cooked) same entry).bound = old.bound := rfl

theorem Cell.rebind_contract (old : Cell source oldExecute oldPolicy oldCooked key) (same) :
    (old.rebind (execute := execute) (policy := policy) (cooked := cooked) same).contract = old.contract := rfl

variable [BEq Key] [LawfulBEq Key] [Hashable Key]

structure Family (source : Source Key Policy Cooked Atom Args Result BuildError)
    (execute : (key : Key) → State → Args key → Except Error (Result key × State)) (policy : Policy) (cooked : Cooked) where
  cells : Std.DHashMap Key (Cell source execute policy cooked)
  built : List Key
  bound : List Key
  reused : List Key

inductive PreparationError (Key BuildError : Type) where
  | duplicate (key : Key)
  | missing (key : Key)
  | construction (key : Key) (error : BuildError)
  deriving Repr

variable (source execute policy cooked)

def Family.step [∀ key, DecidableEq (source.Context key)]
    (old : Option (Family source oldExecute oldPolicy oldCooked)) (entry : Option (PLift (oldExecute = execute)))
    (prior : Family source execute policy cooked) (available : Key → Bool) (key : Key) :
    Except (PreparationError Key BuildError) (Family source execute policy cooked) :=
  if (prior.cells.get? key).isSome then .error (.duplicate key) else
  if !available key then .error (.missing key) else
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
  fresh (install : Cell source execute policy cooked key → Bool → Bool → Family source execute policy cooked) :=
    match compiled : source.construct key (source.project key policy cooked) with
    | .error error => .error (.construction key error)
    | .ok contract => .ok (install ⟨contract,compiled,bind contract (execute key),rfl⟩ true true)

def refresh [∀ key, DecidableEq (source.Context key)]
    (old : Option (Family source oldExecute oldPolicy oldCooked)) (entry : Option (PLift (oldExecute = execute)))
    (available : Key → Bool) : Except (PreparationError Key BuildError) (Family source execute policy cooked) :=
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

structure Snapshot where
  policy : Policy
  cooked : Cooked
  family : Family source execute policy cooked

/-- Preparation and application approval are one immutable publication boundary. -/
def publish [∀ key, DecidableEq (source.Context key)] (old : Snapshot source execute)
    (policy : Policy) (cooked : Cooked) (available : Key → Bool)
    (admit : Family source execute policy cooked → Except AdmissionError Unit) :=
  let outcome : Except (Sum (PreparationError Key BuildError) AdmissionError) (Family source execute policy cooked) := do
    let family ← (refresh source execute policy cooked (some old.family) (some ⟨rfl⟩) available).mapError Sum.inl
    let _ ← (admit family).mapError Sum.inr
    return family
  (outcome,match outcome with | .error _ => old | .ok family => ⟨policy,cooked,family⟩)

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

structure Cache (input : Shared) where
  value : Prepared
  origin : value = projection.prepare input

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

/-- Reuse the existing contract family construction, binding and atomic publisher. -/
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
/-- A direct projection must implement the same closed prepared semantics. -/
def directSource (keys : Policy → Cooked → List Key)
    (direct : (key : Key) → Shared → Context key)
    (construct : (key : Key) → Context key → Except BuildError (Contract (Atom key) (Args key) (Result key))) :
    Source Key Policy Cooked Atom Args Result BuildError where
  Context := Context
  keys := keys
  project := fun key policy cooked => direct key (projection.input policy cooked)
  construct := construct

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
inductive Strategy where | shared | direct deriving BEq, DecidableEq, Repr

def shared (costs : PreparationCosts) (keys : Nat) := costs.prepareCost + keys * costs.sharedCost
def direct (costs : PreparationCosts) (keys : Nat) := keys * costs.directCost

/-- Choose direct only when its modeled saving covers the selector itself. -/
def choose (costs : PreparationCosts) (keys : Nat) : Strategy :=
  if costs.selectionCost + costs.direct keys < costs.shared keys then .direct else .shared

def selected (costs : PreparationCosts) (keys : Nat) :=
  costs.selectionCost + match costs.choose keys with
    | .shared => costs.shared keys
    | .direct => costs.direct keys

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

/-- Actual stage counts are supplied by native traces and semantic admission.
A changed generic/contract is never approved by a cheaper projection policy alone. -/
structure PublicationCosts where
  capture : Nat
  construct : Nat
  bind : Nat
  generic : Nat
  approve : Nat
  deriving Repr

def PublicationCosts.total (prices : PublicationCosts) (preparation built bound generics probes : Nat) :=
  prices.capture + preparation + built * prices.construct + bound * prices.bind +
    generics * prices.generic + probes * prices.approve

theorem publication_direct_bound (costs : PreparationCosts) (keys : Nat)
    (chosen : costs.choose keys = .direct) (prices : PublicationCosts) (built bound generics probes : Nat) :
    prices.total (costs.selected keys) built bound generics probes ≤
      prices.total (costs.shared keys) built bound generics probes := by
  unfold PublicationCosts.total
  have h := costs.direct_covered keys chosen
  omega
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

end PreparationCosts

end LeanPoo.Functional.ContractFamily
