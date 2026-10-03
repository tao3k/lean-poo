import LeanPoo.Object.AncestryTransform
import LeanPoo.Object.Instance

/-! Explicit reversible slot renaming. The new value family is pulled back
along the inverse key map; internal self reads follow the same translation. -/

namespace LeanPoo.Object

universe u v w

/-- A caller-supplied bijection avoids aliases and conflicting renamed writes. -/
structure Renaming (Key : Type u) (NewKey : Type w) where
  forward : Key → NewKey
  inverse : NewKey → Key
  inverse_forward : ∀ key, inverse (forward key) = key
  forward_inverse : ∀ key, forward (inverse key) = key

namespace Renaming

variable {Key : Type u} {NewKey : Type w} {Value : Key → Type v}

abbrev Values (rename : Renaming Key NewKey) (Value : Key → Type v) :=
  fun key => Value (rename.inverse key)

def push (rename : Renaming Key NewKey) (self : Self Key Value) :
    Self NewKey (rename.Values Value) := fun key => self (rename.inverse key)

def pull (rename : Renaming Key NewKey) (self : Self NewKey (rename.Values Value)) :
    Self Key Value := fun key => rename.inverse_forward key ▸ self (rename.forward key)

@[simp] theorem pull_push (rename : Renaming Key NewKey) (self : Self Key Value) :
    rename.pull (rename.push self) = self := by
  funext key
  unfold pull push
  have h : HEq (self (rename.inverse (rename.forward key))) (self key) := by
    rw [rename.inverse_forward]
  apply eq_of_heq
  simpa only [Eq.ndrec, eqRec_heq_iff] using h

@[simp] theorem push_pull (rename : Renaming Key NewKey)
    (self : Self NewKey (rename.Values Value)) : rename.push (rename.pull self) = self := by
  funext key
  unfold push pull
  have h : HEq (self (rename.forward (rename.inverse key))) (self key) := by
    rw [rename.forward_inverse]
  apply eq_of_heq
  simpa only [Eq.ndrec, eqRec_heq_iff] using h

/-- Rename dependent entries without changing ordered-write semantics. -/
def entry {Payload : Key → Type v} [DecidableEq NewKey]
    (rename : Renaming Key NewKey) (source : Entry Key Payload) :
    Entry NewKey (rename.Values Payload) :=
  ⟨rename.forward source.key, cast (congrArg Payload (rename.inverse_forward source.key).symm) source.value,
    fun _ => inferInstance⟩

theorem lookup_entries {Payload : Key → Type v} [DecidableEq NewKey]
    (rename : Renaming Key NewKey) (entries : List (Entry Key Payload)) (key : NewKey) :
    Entry.lookup (entries.map rename.entry) key = Entry.lookup entries (rename.inverse key) := by
  have go (rest : List (Entry Key Payload)) (found : Option (Payload (rename.inverse key))) :
      (rest.map rename.entry).foldl (fun current (entry : Entry NewKey (rename.Values Payload)) =>
        letI : Decidable (key = entry.key) := entry.decideEq key
        if same : key = entry.key then some (same.symm ▸ entry.value) else current) found =
      rest.foldl (fun current (entry : Entry Key Payload) =>
        letI : Decidable (rename.inverse key = entry.key) := entry.decideEq (rename.inverse key)
        if same : rename.inverse key = entry.key then some (same.symm ▸ entry.value)
        else current) found := by
    induction rest generalizing found with
    | nil => rfl
    | cons source rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      dsimp +instances only [entry]
      by_cases same : rename.inverse key = source.key
      · have renamed : key = rename.forward source.key := by
          rw [← same, rename.forward_inverse]
        simp +instances only [dite_eq_left renamed, dite_eq_left same]
        have payload : (renamed.symm ▸ cast (congrArg Payload (rename.inverse_forward source.key).symm) source.value) = (same.symm ▸ source.value) := by
          apply eq_of_heq
          simpa only [Eq.ndrec, eqRec_heq_iff, heq_eqRec_iff] using (cast_heq (congrArg Payload (rename.inverse_forward source.key).symm) source.value)
        simpa +instances only [payload] using ih (some (same.symm ▸ source.value))
      · have renamed : key ≠ rename.forward source.key := by
          intro h
          apply same
          rw [h, rename.inverse_forward]
        simpa +instances only [dite_eq_right renamed, dite_eq_right same] using ih found
  exact go entries none

def slots (rename : Renaming Key NewKey) (key : Key)
    (spec : SlotPayload Key Value key) :
    Prototype.SlotSpec (Self NewKey (rename.Values Value)) (Option (Value key)) :=
  .computed fun self inherited => spec.eval (rename.pull self) inherited

/-- Translate the complete declaration, including defaults and internal self. -/
def declaration [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Declaration Key Value) : Declaration NewKey (rename.Values Value) :=
  { slots := (source.slots.map (Entry.mapPayload rename.slots)).map rename.entry
    defaults := source.defaults.map rename.entry }

theorem declaration_default [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Declaration Key Value) (key : NewKey) :
    (rename.declaration source).default key = source.default (rename.inverse key) :=
  rename.lookup_entries source.defaults key

theorem declaration_slot [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Declaration Key Value) (key : NewKey) :
    (rename.declaration source).slot key =
      (source.slot (rename.inverse key)).map (rename.slots (rename.inverse key)) := by
  rw [Declaration.slot, declaration, rename.lookup_entries, Entry.lookup_mapPayload]
  rfl

/-- Rename every declaration in the schema; prototype identities stay fixed. -/
def schema [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Schema Key Value) : Schema NewKey (rename.Values Value) :=
  { graph := source.graph
    declaration := fun name => (source.declaration name).map rename.declaration }

def plan [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Plan Key Value) : Plan NewKey (rename.Values Value) :=
  { schema := rename.schema source.schema
    root := source.root
    precedence := source.precedence
    valid := source.valid }

/-- Renaming commutes with the complete C4 resolver for every final self. -/
theorem resolve [DecidableEq NewKey] (rename : Renaming Key NewKey)
    (source : Plan Key Value) (key : NewKey)
    (self : Self NewKey (rename.Values Value)) :
    (rename.plan source).resolve key self =
      source.resolve (rename.inverse key) (rename.pull self) := by
  have defaults (names : List String) :
      names.foldr ((rename.schema source.schema).defaultStep key) none =
      names.foldr (source.schema.defaultStep (rename.inverse key)) none := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
      simp only [List.foldr_cons, Schema.defaultStep, schema, Option.map]
      cases source.schema.declaration name with
      | none => exact ih
      | some d =>
        simp only []
        rw [rename.declaration_default]
        cases d.default (rename.inverse key) with
        | none => exact ih
        | some value => rfl
  have methods (names : List String) :
      names.foldr ((rename.schema source.schema).methodStep key) Prototype.Method.identity =
      fun receiver inherited =>
        (names.foldr (source.schema.methodStep (rename.inverse key))
          Prototype.Method.identity) (rename.pull receiver) inherited := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
      simp only [List.foldr_cons, Schema.methodStep, schema, Option.map]
      cases source.schema.declaration name with
      | none => exact ih
      | some d =>
        simp only []
        rw [rename.declaration_slot]
        cases d.slot (rename.inverse key) with
        | none => exact ih
        | some spec =>
          simp only [Option.map_some]
          simp only [schema, Option.map] at ih
          rw [ih]
          rfl
  rw [Plan.resolve_eq_compileSlot, Plan.resolve_eq_compileSlot,
    Plan.compileSlot_apply, Plan.compileSlot_apply]
  dsimp only [plan]
  rw [methods, defaults]

/-- A proof-bearing fixed point transports without tying another unsafe knot. -/
def instantiate [DecidableEq NewKey] (rename : Renaming Key NewKey)
    {source : Plan Key Value} (original : Instance Key Value source) :
    Instance NewKey (rename.Values Value) (rename.plan source) :=
  { state := rename.push original.state
    agrees := by
      intro key
      rw [rename.resolve, rename.pull_push, original.agrees]
      rfl }

/-- Rebuild translated lazy cells using the original resolution strategy. -/
def memoized [DecidableEq NewKey]
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    [BEq NewKey] [LawfulBEq NewKey] [Hashable NewKey]
    (rename : Renaming Key NewKey) (original : Memoized Key Value) :
    Memoized NewKey (rename.Values Value) :=
  (rename.plan original.plan).memoizeUsing original.mode

end Renaming
end LeanPoo.Object
