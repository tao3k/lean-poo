import LeanPoo.Proof.Revision

/-!
A proof-bearing persistent runtime value. Mutation can store this value in a
cell, while all revision and certificate work remains a pure operation.
-/

namespace LeanPoo.Proof

/-- One C4 plan, its certified instance, and the explicit value cache for
selected keys. The cache is indexed by that exact instance. -/
structure Runtime (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  plan : Object.Plan Key Value
  certified : CertifiedObject Key Value plan
  keys : List Key
  cache : Object.Cache
    (certified.instanceValue.prepare keys)
    certified.instanceValue.state

def Runtime.new {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    (certified : CertifiedObject Key Value plan)
    (keys : List Key) : Runtime Key Value :=
  { plan
    certified
    keys
    cache := certified.instanceValue.cache keys }

/-- Prepare selected evaluated values before sharing a runtime snapshot. -/
def Runtime.newLoaded {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    (certified : CertifiedObject Key Value plan)
    (keys loaded : List Key) : Runtime Key Value :=
  { plan
    certified
    keys
    cache := (certified.instanceValue.cache keys).force loaded }

/-- A read returns a new persistent runtime with its evaluated cache entry. -/
def Runtime.read {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) (key : Key) :
    Option (Value key) × Runtime Key Value :=
  let (value, cache) := runtime.cache.read key
  (value, { runtime with cache })

theorem Runtime.read_sound {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) (key : Key) :
    (runtime.read key).1 = runtime.certified.instanceValue.state key := by
  change (runtime.cache.read key).1 = _
  exact runtime.certified.instanceValue.cachedRead runtime.keys runtime.cache key

/-- A complete pure revision: infer the next fixed point, rebase evaluated
values, select pending obligations, and close the new certificate. -/
def Runtime.revise {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value)
    {newPlan : Object.Plan Key Value}
    (spec : Object.Dependencies Key Value newPlan)
    (roots : List Key)
    (sameResolver : ∀ key, key ∉ roots →
      runtime.plan.resolve key runtime.certified.instanceValue.state =
        newPlan.resolve key runtime.certified.instanceValue.state)
    (obligations : List (Obligation Key (fun key => Option (Value key))) := [])
    (discharged : ∀ revision : Object.Revision spec roots runtime.keys,
      ∀ obligation,
        obligation ∈ pendingRevision runtime.certified revision obligations →
        obligation.holds revision.instanceValue.state) :
    Except (Object.RevisionError Key) (Runtime Key Value) :=
  match spec.revise roots runtime.certified.instanceValue runtime.keys
      runtime.cache sameResolver with
  | .error error => .error error
  | .ok revision =>
      let certified := runtime.certified.applyRevision revision
        sameResolver obligations (discharged revision)
      .ok {
        plan := newPlan
        certified
        keys := runtime.keys
        cache := revision.cache
      }

/-- A versioned identity for certified persistent runtime values. Cache reads
update the installed value without advancing the semantic revision version. -/
structure MutableRuntime (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  cell : IO.Ref (Nat × Runtime Key Value)

def MutableRuntime.new {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) : IO (MutableRuntime Key Value) := do
  return ⟨← IO.mkRef (0, runtime)⟩

def MutableRuntime.snapshot {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (mutable : MutableRuntime Key Value) : IO (Nat × Runtime Key Value) :=
  mutable.cell.get

/-- A read atomically memoizes a certified value in the current runtime. -/
def MutableRuntime.read {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (mutable : MutableRuntime Key Value) (key : Key) : IO (Option (Value key)) :=
  mutable.cell.modifyGet fun (version, runtime) =>
    let (value, next) := runtime.read key
    (value, (version, next))

/-- Install a pure, fully certified revision only if the snapshot from which
it was derived is still current. A stale install leaves the cell unchanged. -/
def MutableRuntime.install {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (mutable : MutableRuntime Key Value)
    (expectedVersion : Nat) (next : Runtime Key Value) : IO Bool :=
  mutable.cell.modifyGet fun (version, current) =>
    if version == expectedVersion then
      (true, (version + 1, next))
    else
      (false, (version, current))

/-- Run a pure certified update against the current value in one cell
operation. An error preserves both its version and cached contents. -/
def MutableRuntime.transact {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (mutable : MutableRuntime Key Value)
    (update : Runtime Key Value → Except ε (Runtime Key Value)) :
    IO (Except ε Unit) :=
  mutable.cell.modifyGet fun (version, current) =>
    match update current with
    | .error error => (.error error, (version, current))
    | .ok next => (.ok (), (version + 1, next))

end LeanPoo.Proof
