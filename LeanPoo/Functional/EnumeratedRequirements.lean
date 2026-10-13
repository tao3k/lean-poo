import LeanPoo.Prototype.RecordRepresentations
import LeanPoo.Functional.ResultView

/-! Prepare a runtime key-list slot and its heterogeneous factory slots as one
aligned catalog. Source order and duplicates remain observable; undeclared
capabilities are excluded from the built consumer record. -/
namespace LeanPoo.Functional.EnumeratedRequirements
open Prototype Requirements
variable {Context Key : Type} {Value : Context → Key → Type}

abbrev Catalog (Context Key : Type) (Value : Context → Key → Type) :=
  KeyedPrototype.Rec (fun key => Factory Context (fun context => Value context key))

def provider (catalog : Catalog Context Key Value) : Provider Context Key Value :=
  fun key => catalog.lookup (.inl key)

inductive Error (Key : Type) where
  | missingKeys | missing (key : Key)
  deriving BEq, Repr

structure Prepared (catalog : Catalog Context Key Value) where
  keys : List Key
  factories : Factories Context Value keys
  declared : catalog.lookup (.inr ()) = some keys
  selected : Selected (provider catalog) keys factories

/-- Read the final introspection slot first, then prepare in that exact order.
Selection retains function values and does not apply their bodies. -/
def prepare (catalog : Catalog Context Key Value) : Except (Error Key) (Prepared catalog) :=
  match declared : catalog.lookup (.inr ()) with
  | none => .error .missingKeys
  | some keys => match found : Requirements.prepare (provider catalog) keys with
    | .error key => .error (.missing key)
    | .ok factories => .ok ⟨keys, factories, declared, (prepare_ok_iff _ _ _).mp found⟩

def Prepared.forget {catalog : Catalog Context Key Value} (ready : Prepared catalog) :
    (keys : List Key) × Factories Context Value keys := ⟨ready.keys, ready.factories⟩

/-- Exact successful tuples and errors agree with reading the source key slot
and ordinary requirement preparation, without erasing duplicates or order. -/
theorem prepare_source (catalog : Catalog Context Key Value) :
    (prepare catalog).map Prepared.forget =
      match catalog.lookup (.inr ()) with
      | none => .error .missingKeys
      | some keys => ((Requirements.prepare (provider catalog) keys).mapError Error.missing).map
          (fun factories => ⟨keys, factories⟩) := by
  unfold prepare
  split <;> rename_i declared
  · conv => rhs; rw [declared]
    rfl
  · conv => rhs; rw [declared]
    dsimp only
    split <;> rename_i found
    · conv => rhs; rw [found]
      rfl
    · conv => rhs; rw [found]
      rfl

theorem prepare_missingKeys_iff (catalog : Catalog Context Key Value) :
    prepare catalog = .error .missingKeys ↔ catalog.lookup (.inr ()) = none := by
  unfold prepare
  split
  · simp_all
  · split <;> simp_all

theorem prepare_missing_iff (catalog : Catalog Context Key Value) (key : Key) :
    prepare catalog = .error (.missing key) ↔
      ∃ keys, catalog.lookup (.inr ()) = some keys ∧
        Requirements.prepare (provider catalog) keys = .error key := by
  unfold prepare
  split <;> rename_i declared
  · simp_all
  · split <;> rename_i found <;> simp_all

variable [DecidableEq Key]

/-- Store built values once in a narrow function record. A runtime declaration
restricts this record's interface even if the catalog has extra value slots. -/
def Prepared.buildRecord {catalog : Catalog Context Key Value} (ready : Prepared catalog)
    (context : Context) : Record Key (Value context) :=
  let data := build ready.factories context
  { lookup := fun key => if included : key ∈ ready.keys then some (resultAt data key included) else none }

theorem Prepared.buildRecord_present {catalog : Catalog Context Key Value} (ready : Prepared catalog)
    (context : Context) (key : Key) (member : key ∈ ready.keys) :
    (ready.buildRecord context).lookup key = some (factoryAt ready.factories key member context) := by
  simp [buildRecord, member, resultAt_build]

theorem Prepared.buildRecord_absent {catalog : Catalog Context Key Value} (ready : Prepared catalog)
    (context : Context) (key : Key) (absent : key ∉ ready.keys) :
    (ready.buildRecord context).lookup key = none := by simp [buildRecord, absent]

theorem Prepared.producer {catalog : Catalog Context Key Value} (ready : Prepared catalog)
    (context : Context) (key : Key) (member : key ∈ ready.keys) :
    ∃ factory, catalog.lookup (.inl key) = some factory ∧
      (ready.buildRecord context).lookup key = some (factory context) :=
  ⟨factoryAt ready.factories key member,
    factoryAt_selected (provider catalog) ready.keys ready.factories ready.selected key member,
    ready.buildRecord_present context key member⟩

/-- Consumer order and repeated keys are preserved when projecting retained
factories; no source catalog is consulted again. -/
theorem Prepared.project_ready {catalog : Catalog Context Key Value} (ready : Prepared catalog)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ ready.keys) :
    Requirements.prepare (provider catalog) keys = .ok (project ready.factories keys included) :=
  Requirements.project_ready _ _ ((prepare_ok_iff _ _ _).mpr ready.selected) keys included

/-- The source's default key exposure publishes child-before-parent lists;
ordinary factory slots retain the actual composed layer's observations. -/
theorem withKeys_source
    (definition : KeyedPrototype.Definition Key (fun key => Factory Context (fun context => Value context key)))
    (self parent : Thunk (Catalog Context Key Value)) :
    (definition.withKeys false self parent).lookup (.inr ()) = some definition.keys ∧
      ∀ key, provider (definition.withKeys false self parent) key = provider (definition.layer self parent) key :=
  ⟨definition.withKeys_keys self parent, fun key => definition.withKeys_values self parent key⟩

end LeanPoo.Functional.EnumeratedRequirements
