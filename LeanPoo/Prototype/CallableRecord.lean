import LeanPoo.Prototype.MutableRecord
import LeanPoo.Prototype.RecursiveReindex
import LeanPoo.Prototype.DynamicValueEquality
import Std.Data.HashMap.Lemmas

/-! Safe record methods with parameters, final-self calls and lazy inherited
methods. The existing recursive evaluator owns all computation and sharing;
the complete method name/argument request is its cache and cycle key. -/
namespace LeanPoo.Prototype.CallableRecord

open Recursive
abbrev Value := Dynamic.Value

structure Request (Argument : Type) where
  name : String
  argument : Argument
  deriving Repr, BEq, DecidableEq

abbrev Self (Argument : Type) := Generator (Request Argument) Value
abbrev Method (Argument : Type) := Argument → Interaction (Request Argument) Value Value
abbrev Storage (Argument : Type) := Std.HashMap String (Method Argument)
abbrev Layer (Argument : Type) := Proto (Self Argument) (Unit → Method Argument) (Method Argument)
abbrev Specification (Argument : Type) := Proto (Self Argument) (Storage Argument) (Storage Argument)

def generator (storage : Storage Argument) : Self Argument := fun input =>
  ((storage.get? input.name).getD (fun _ => .error s!"missing slot: {input.name}")) input.argument

def method (key : String) (layer : Layer Argument) : Specification Argument :=
  fun self storage => storage.insert key (layer self (fun _ => fun argument =>
    generator storage ⟨key, argument⟩))

def constant (value : Value) : Layer Argument := fun _ _ _ => .value value

def compute (body : Self Argument → Method Argument) : Layer Argument := fun self _ => body self

def modify (body : Argument → Value → Value) : Layer Argument :=
  fun _ inherited argument => ((inherited ()) argument).map (body argument)

def readPure (storage : Storage Argument) (depth : Nat) (input : Request Argument) : Observation Value :=
  solve (generator storage) depth input

/-- A data slot uses the distinguished field argument for all self reads.
The original interaction tree is retained, including missing-slot errors. -/
def ofFields (storage : MutableRecord.Storage) (fieldArgument : Argument) : Storage Argument :=
  storage.map fun _ tree => fun _ => tree.relabel (fun key => ⟨key, fieldArgument⟩)

theorem generator_ofFields (storage : MutableRecord.Storage) (fieldArgument : Argument) :
    generator (ofFields storage fieldArgument) =
      (MutableRecord.generator storage).reindex Request.name (fun key => ⟨key, fieldArgument⟩) := by
  funext input
  simp only [generator, ofFields, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map,
    Generator.reindex, MutableRecord.generator]
  cases storage[input.name]? <;> rfl

/-- Existing value-only records preserve every finite observation in the
method protocol, for every supplied argument, source error and pending read. -/
theorem readPure_ofFields (storage : MutableRecord.Storage) (fieldArgument : Argument)
    (depth : Nat) (input : Request Argument) :
    readPure (ofFields storage fieldArgument) depth input =
      MutableRecord.readPure storage depth input.name := by
  unfold readPure MutableRecord.readPure
  rw [generator_ofFields]
  exact solve_reindex _ _ _ (fun _ => rfl) depth input

structure Snapshot (Argument : Type) where
  storage : Storage Argument
  generation : Nat := 0

private structure MutableState (Argument : Type) where
  snapshot : Snapshot Argument
  memo : Cached.Cache (generator snapshot.storage) := {}

structure Mutable (Argument : Type) where private mk ::
  private cell : Std.Mutex (MutableState Argument)

def create (base : Storage Argument) : IO (Mutable Argument) := do
  return ⟨← Std.Mutex.new ⟨⟨base, 0⟩, {}⟩⟩

def Mutable.snapshot (object : Mutable Argument) : IO (Snapshot Argument) :=
  object.cell.atomically do return (← get).snapshot

/-- Install one inherited method while retaining the same mutable identity.
The old method is captured lazily; every final-self call sees the new snapshot. -/
def Mutable.slot (object : Mutable Argument) (key : String) (layer : Layer Argument) : IO Unit :=
  object.cell.atomically do
    let state ← get
    let snapshot : Snapshot Argument :=
      ⟨method key layer request state.snapshot.storage, state.snapshot.generation + 1⟩
    set (⟨snapshot, {}⟩ : MutableState Argument)

def Mutable.callCertified [DecidableEq Argument] (object : Mutable Argument)
    (budget : Nat) (input : Request Argument) :
    IO (Σ snapshot : Snapshot Argument, Except (Cached.Failure (generator snapshot.storage) input)
      (Cached.Receipt (generator snapshot.storage) (generator snapshot.storage input))) :=
  object.cell.atomically do
    let state ← get
    match Cached.runCertified (generator state.snapshot.storage) input budget state.memo with
    | .error failure => return ⟨state.snapshot, .error failure⟩
    | .ok (receipt, memo) =>
      set (⟨state.snapshot, memo⟩ : MutableState Argument)
      return ⟨state.snapshot, .ok receipt⟩

def Mutable.cachedRequests (object : Mutable Argument) : IO (List (Request Argument)) :=
  object.cell.atomically do return (← get).memo.entries.map Cached.Entry.input

def Mutable.statistics (object : Mutable Argument) : IO Cached.Statistics :=
  object.cell.atomically do return (← get).memo.statistics

end LeanPoo.Prototype.CallableRecord
