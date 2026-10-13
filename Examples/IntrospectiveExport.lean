import LeanPoo.Functional.EnumeratedRequirements
import LeanPoo.Prototype.RecordDescription

/-! Compose heterogeneous keyed factory prototypes, prepare their runtime
declarations, build a narrow typed record, then use the same declarations for
generated inspection. A keys-slot interceptor changes the public interface. -/
namespace LeanPoo.Examples.IntrospectiveExport
open Functional Prototype

inductive Capability where
  | quota | endpoint | report | missing
  deriving DecidableEq, BEq, Repr
def Value (budget : Nat) : Capability → Type
  | .quota => {amount : Nat // amount ≤ budget}
  | .endpoint | .report | .missing => String
abbrev Catalog := EnumeratedRequirements.Catalog Nat Capability Value
abbrev Definition := KeyedPrototype.Definition Capability (fun key => Factory Nat (fun c => Value c key))

def quota : Factory Nat (fun c => Value c .quota) := fun c => ⟨c/3, Nat.div_le_self _ _⟩
def oldQuota : Factory Nat (fun c => Value c .quota) := fun c => ⟨c/2, Nat.div_le_self _ _⟩
def endpoint : Factory Nat (fun c => Value c .endpoint) := fun _ => "production"
def report : Factory Nat (fun c => Value c .report) := fun c => String.append "production" (String.append ":" (Nat.repr (c/3)))

def parent : Definition := KeyedPrototype.compose (KeyedPrototype.slot .endpoint endpoint)
  (KeyedPrototype.slot .quota oldQuota)
def child : Definition := KeyedPrototype.compose
  ⟨Object.recordSlotGen (.inl .report) (fun self _ => do
      let capacity ← self.get.lookup (.inl .quota)
      let address ← self.get.lookup (.inl .endpoint)
      return fun c => String.append (address c) (String.append ":" (Nat.repr (capacity c).val))), [.report]⟩
  (KeyedPrototype.slot .quota quota)

abbrev allKeys : List Capability := [.report, .quota, .endpoint, .quota]
abbrev publicKeys : List Capability := [.report, .quota]
def definition : Definition :=
  let layers := KeyedPrototype.compose child parent
  { layers with layer := DelayedProto.compose (KeyedPrototype.expose publicKeys) layers.layer }

def self : Catalog := { lookup := fun key => match key with
  | .inl .quota => some quota
  | .inl .endpoint => some endpoint
  | .inl .report => some report
  | .inl .missing => none
  | .inr () => some allKeys }
def catalog (allowOverride : Bool) : Catalog := definition.withKeys allowOverride (Thunk.pure self)
  (Thunk.pure Record.empty)

theorem declared_default : (catalog false).lookup (.inr ()) = some allKeys :=
  definition.withKeys_keys _ _
theorem declared_public : (catalog true).lookup (.inr ()) = some publicKeys := by
  simp [catalog, definition, KeyedPrototype.Definition.withKeys, DelayedProto.compose, KeyedPrototype.expose,
    Object.recordSlotGen]

/-- The actual composed prototypes use the final quota/endpoint in the report,
and both introspection policies preserve every ordinary factory slot. -/
theorem source_lookup (allowOverride : Bool) (key : Capability) :
    EnumeratedRequirements.provider (catalog allowOverride) key = EnumeratedRequirements.provider self key := by
  cases allowOverride <;> cases key <;>
    simp [EnumeratedRequirements.provider, catalog, definition, child, parent, KeyedPrototype.Definition.withKeys, KeyedPrototype.compose,
      KeyedPrototype.slot, KeyedPrototype.expose, Object.recordSlotGen, DelayedProto.compose,
      Thunk.get, Thunk.pure, self, quota, endpoint, Record.empty]
  all_goals rfl

def label : Capability → String
  | .quota => "quota" | .endpoint => "endpoint" | .report => "report" | .missing => "missing"
def description (budget : Nat) (keys : List Capability) : RecordDescription Capability (Value budget) :=
  ⟨"Deployment", keys, label, fun key => match key with
    | .quota => {
        name := s!"quota ≤ {budget}"
        accepts := fun value => decide (value.val ≤ budget)
        display := fun value => toString value.val }
    | .endpoint | .report | .missing => Descriptor.top "Text" id⟩

theorem built_valid (allowOverride : Bool) (ready : EnumeratedRequirements.Prepared (catalog allowOverride)) (budget : Nat) :
    (description budget ready.keys).accepts (ready.buildRecord budget) = true := by
  apply List.all_eq_true.mpr
  intro key member
  rw [ready.buildRecord_present budget key member]
  cases key <;> simp [description, Descriptor.top]
  exact (Requirements.factoryAt ready.factories .quota member budget).property

def scenario (allowOverride : Bool) (budget : Nat) : Except (Sum (EnumeratedRequirements.Error Capability) String)
    (List String × Option Nat × Option String × Bool × Lean.Json) := do
  let ready ← (EnumeratedRequirements.prepare (catalog allowOverride)).mapError Sum.inl
  let built := ready.buildRecord budget
  let inspected ← ((description budget ready.keys).inspect built).mapError Sum.inr
  return (ready.keys.map label, (built.lookup .quota).map Subtype.val, built.lookup .report,
    (built.lookup .endpoint).isSome, inspected)

#guard ((scenario false 8).toOption.map fun out => (out.1, out.2.1, out.2.2.1, out.2.2.2.1)) ==
  some (["report", "quota", "endpoint", "quota"], some 2, some "production:2", true)
#guard ((scenario true 8).toOption.map fun out => (out.1, out.2.1, out.2.2.1, out.2.2.2.1)) ==
  some (["report", "quota"], some 2, some "production:2", false)
#guard (EnumeratedRequirements.prepare ({ lookup := fun _ => none } : Catalog)).toOption.isNone
#guard ((description 8 allKeys).schema.getObjValAs? (Array Lean.Json) "fields").toOption.map Array.size == some 4
#guard ((scenario false 8).toOption.bind fun out => (out.2.2.2.2.getObjValAs? String "report").toOption) == some "production:2"
#guard ((scenario true 8).toOption.bind fun out => (out.2.2.2.2.getObjVal? "endpoint").toOption).isNone
#eval IO.println s!"default introspection: {(scenario false 8).toOption.map (fun out => out.2.2.2.2.compress)}; public: {(scenario true 8).toOption.map (fun out => out.2.2.2.2.compress)}"

end LeanPoo.Examples.IntrospectiveExport

#print axioms LeanPoo.Examples.IntrospectiveExport.source_lookup
#print axioms LeanPoo.Examples.IntrospectiveExport.built_valid
