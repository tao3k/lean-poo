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

end LeanPoo.Functional.ContractFamily
