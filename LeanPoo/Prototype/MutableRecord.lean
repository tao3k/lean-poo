import LeanPoo.Prototype.RecursiveCache
import LeanPoo.Prototype.DynamicDescriptor
import LeanPoo.Prototype.LinearState
import Std.Data.HashMap

/-! The paper's `fix!`/`mix!` protocol over one mutable hash identity.
The stored effective slot computations contain explicit final-self requests
and captured inherited syntax. Updating a slot therefore needs one table
insertion, without relinearizing or reconstructing the object. -/
namespace LeanPoo.Prototype.MutableRecord

open Recursive
abbrev Value := Dynamic.Value
abbrev Slot := Interaction String Value Value
abbrev Storage := Std.HashMap String Slot
abbrev Self := Generator String Value
abbrev SlotLayer := Proto Self Slot Slot

def generator (storage : Storage) : Self := fun key =>
  (storage.get? key).getD (.error s!"missing slot: {key}")

def readPure (storage : Storage) (depth : Nat) (key : String) : Observation Value :=
  solve (generator storage) depth key

def write (storage : Storage) (key : String) (layer : SlotLayer) : Storage :=
  storage.insert key (layer request (generator storage key))

/-- A pure prototype retains the same final-self and inherited-slot meanings. -/
def pureSlot (key : String) (layer : SlotLayer) : Proto Self Storage Storage :=
  fun self inherited => inherited.insert key (layer self (generator inherited key))

theorem write_pureSlot (storage : Storage) (key : String) (layer : SlotLayer) :
    write storage key layer = pureSlot key layer request storage := rfl

/-- Persistent values convert to mutable effective slots without changing
their value types or admitting unknown/uninitialized slots. -/
def fromValues (values : List (String × Value)) : Storage :=
  values.foldl (fun storage entry => storage.insert entry.1 (.value entry.2)) {}

inductive Specification where
  | identity
  | slot (key : String) (layer : SlotLayer)
  | compose (child parent : Specification)
  | error (message : String)

/-- Pure state threading includes the state retained when an effect fails.
This is the value semantics of the mutable protocol, including partial writes. -/
def Specification.transition : Specification → Storage → Storage × Except String Unit
  | .identity, storage => (storage, .ok ())
  | .slot key layer, storage => (write storage key layer, .ok ())
  | .error message, storage => (storage, .error message)
  | .compose child parent, storage =>
    let (inherited, status) := parent.transition storage
    match status with
    | .error message => (inherited, .error message)
    | .ok _ => child.transition inherited

def Specification.composeAll (layers : List Specification) : Specification :=
  layers.foldr Specification.compose .identity

theorem Specification.compose_assoc (outer middle inner : Specification) (storage : Storage) :
    (Specification.compose (Specification.compose outer middle) inner).transition storage =
      (Specification.compose outer (Specification.compose middle inner)).transition storage := by
  simp only [Specification.transition]
  cases first : inner.transition storage with
  | mk inherited status =>
    cases status with
    | error message => rfl
    | ok value =>
      cases second : middle.transition inherited with
      | mk inheritedAgain status => cases status <;> rfl

structure Snapshot where
  storage : Storage
  generation : Nat := 0

private structure MutableState where
  snapshot : Snapshot
  memo : Cached.Cache (generator snapshot.storage) := {}

structure Mutable where private mk ::
  private cell : Std.Mutex MutableState

/-- `hash-copy` means a fresh mutable identity sharing only immutable storage. -/
def create (base : Storage) : IO Mutable := do
  return ⟨← Std.Mutex.new ⟨⟨base, 0⟩, {}⟩⟩

/-- Conversion to pure state is a retained immutable snapshot. -/
def Mutable.snapshot (object : Mutable) : IO Storage :=
  object.cell.atomically do return (← get).snapshot.storage

def Mutable.generation (object : Mutable) : IO Nat :=
  object.cell.atomically do return (← get).snapshot.generation

def Mutable.read (object : Mutable) (depth : Nat) (key : String) : IO (Observation Value) := do
  return readPure (← object.snapshot) depth key

/-- One slot update captures the previous effective computation and retains
the same cell as final-self identity. Self requests resolve on each later read. -/
def Mutable.slot (object : Mutable) (key : String) (layer : SlotLayer) : IO Unit :=
  object.cell.atomically do
    let state ← get
    let snapshot : Snapshot :=
      ⟨write state.snapshot.storage key layer, state.snapshot.generation + 1⟩
    set (⟨snapshot, {}⟩ : MutableState)

/-- Each successful force carries an evaluation proof for the exact immutable
snapshot read while holding the mutex. Slot writes clear all memo entries and
advance the generation; stale computations cannot inhabit the new cache. -/
def Mutable.force (object : Mutable) (budget : Nat) (key : String) :
    IO (Except (Cached.Diagnostic String) (Σ snapshot : Snapshot,
      Cached.Receipt (generator snapshot.storage) (generator snapshot.storage key))) :=
  object.cell.atomically do
    let state ← get
    match Cached.run (generator state.snapshot.storage) key budget state.memo with
    | .error diagnostic => return .error diagnostic
    | .ok (receipt, memo) =>
      set (⟨state.snapshot, memo⟩ : MutableState)
      return .ok ⟨state.snapshot, receipt⟩

def Mutable.cachedKeys (object : Mutable) : IO (List String) :=
  object.cell.atomically do return (← get).memo.entries.map Cached.Entry.input

def Mutable.statistics (object : Mutable) : IO Cached.Statistics :=
  object.cell.atomically do return (← get).memo.statistics

def Specification.apply : Specification → Mutable → IO (Except String Unit)
  | .identity, _ => pure (.ok ())
  | .slot key layer, object => do
    object.slot key layer
    return .ok ()
  | .error message, _ => pure (.error message)
  | .compose child parent, object => do
    match ← parent.apply object with
    | .error message => return .error message
    | .ok _ => child.apply object

/-- POOF `fix!`: allocate one fresh identity, apply all mutations, return it. -/
def instantiate (prototype : Specification) (base : Storage) : IO (Except String Mutable) := do
  let object ← create base
  match ← prototype.apply object with
  | .error message => return .error message
  | .ok _ => return .ok object

/-- The same pure transition is available through consume-old state references.
On failure the old linear reference remains valid, following LinearState's policy. -/
def Specification.applyLinear (specification : Specification) (state : LinearState Storage) :
    IO (Except String (LinearState Storage)) :=
  state.step fun storage =>
    let (next, status) := specification.transition storage
    status.map (fun _ => next)

def constant (value : Value) : SlotLayer := fun _ _ => .value value

def compute (function : Self → Slot) : SlotLayer := fun self _ => function self

def modify (function : Value → Value) : SlotLayer :=
  fun _ inherited => inherited.map function

/-- A pure snapshot observes the unbounded recursive slot semantics exactly. -/
theorem read_returns_iff (storage : Storage) (key : String) (value : Value) :
    (∃ depth, readPure storage depth key = .value value) ↔
      Evaluates (generator storage) (generator storage key) (.value value) :=
  returns_iff_evaluates _ _ _

end LeanPoo.Prototype.MutableRecord
