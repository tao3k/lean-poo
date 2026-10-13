import LeanPoo.Functional.MetadataFamily
import LeanPoo.Functional.EnumeratedRequirements

namespace LeanPoo.Tests.FunctionalReflectiveRequirements
open Functional Prototype

private instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq left right := match left, right with
    | .error a, .error b => a == b
    | .ok a, .ok b => a == b
    | _, _ => false

abbrev Fields := FactoryRecord Nat String (fun _ _ => Nat)
def blank : Fields := Record.empty
def numeric (key : String) (factory : Nat → Nat) : MetaPrototype.Layer Fields :=
  Object.recordSlotGen key (fun _ _ => some factory)
def common : MetaPrototype.Layer Fields :=
  DelayedProto.compose (numeric "capacity" (·+10))
    (DelayedProto.compose (Object.recordSlotGen "used" (fun self _ => self.get.lookup "capacity"))
      (numeric "owner" (fun _ => 0)))
def wrap (change : Nat → Nat) : MetaPrototype.Layer Fields :=
  Object.recordSlotGen "used" (fun _ old => old.get.map (fun factory => fun c => change (factory c)))
def west (fee : Nat) : MetaPrototype.Layer Fields :=
  DelayedProto.compose (wrap (·+fee)) (numeric "owner" (fun _ => 1))
def audit (scale : Nat) : MetaPrototype.Layer Fields :=
  DelayedProto.compose (wrap (·*scale)) (numeric "owner" (fun _ => 2))
def parent (layer : MetaPrototype.Layer Fields) (supers order : List String) : MetaPrototype.Instance Fields :=
  ⟨Thunk.pure blank, some (MetadataFamily.constantMetadata layer supers order), fun _ old => old.get⟩
def registry (fee scale : Nat) : MetaPrototype.Registry Fields := [
  ("Common", parent common [] ["Common"]),
  ("West", parent (west fee) ["Common"] ["West", "Common"]),
  ("Audit", parent (audit scale) ["Common"] ["Audit", "Common"])]
def checked (reverse : Bool) (extra fee scale : Nat) :=
  MetaPrototype.prepareChecked "Root"
    (MetadataFamily.constantMetadata (numeric "capacity" (·+extra))
      (if reverse then ["Audit", "West"] else ["West", "Audit"]) []) (registry fee scale)
def self (extra : Nat) : Fields := { lookup := fun key => if key == "capacity" then some (·+extra) else none }
def flattenNumbers {context : Nat} {keys : List String}
    (data : Requirements.Results (fun (_ : Nat) (_ : String) => Nat) context keys) : List Nat :=
  match keys, data with
  | [], _ => []
  | _ :: _, (head, tail) => head :: flattenNumbers tail

-- Independent arithmetic and ordered list recursion; no prototype, C3,
-- factory selection, retained tuple or build methods occur in this model.
def expected (reverse : Bool) (extra fee scale context : Nat) : List String → Except String (List Nat)
  | [] => .ok []
  | key :: rest =>
    let value := if key == "capacity" then some (context+extra)
      else if key == "used" then some (if reverse then (context+extra+fee)*scale else (context+extra)*scale+fee)
      else if key == "owner" then some (if reverse then 2 else 1) else none
    match value with
    | none => .error key
    | some value => (expected reverse extra fee scale context rest).map (value :: ·)

def checkMetadata : IO Nat := do
  let mut count := 0
  for reverse in [false, true] do
    for extra in [0, 4] do
      for scale in [0, 2] do
        for fee in [0, 1, 3] do
          let plan ← IO.ofExcept (checked reverse extra fee scale)
          unless plan.order == (if reverse then ["Root", "Audit", "West", "Common"] else ["Root", "West", "Audit", "Common"]) do
            throw (IO.userError "captured diamond order")
          for context in [0, 1, 7, 10] do
            for keys in [[], ["capacity"], ["used", "capacity", "used"], ["absent", "used"],
                ["used", "missing", "capacity"], ["capacity", "used", "owner"]] do
              let actual := (MetadataFamily.prepareOpen plan (self extra) blank keys).map
                (fun factories => flattenNumbers (Requirements.build factories context))
              unless actual == expected reverse extra fee scale context keys do
                throw (IO.userError "source C3 factory composition / ordered tuple / first missing")
              count := count+1
  return count

inductive Key where
  | quota | endpoint | report | missing
  deriving DecidableEq, BEq, Repr
def Value (budget : Nat) : Key → Type
  | .quota => {amount : Nat // amount ≤ budget}
  | .endpoint | .report | .missing => String
abbrev Catalog := EnumeratedRequirements.Catalog Nat Key Value
abbrev Definition := KeyedPrototype.Definition Key (fun key => Factory Nat (fun c => Value c key))
def quota : Factory Nat (fun c => Value c .quota) := fun c => ⟨c/3, Nat.div_le_self _ _⟩
def oldQuota : Factory Nat (fun c => Value c .quota) := fun c => ⟨c/2, Nat.div_le_self _ _⟩
def address : Factory Nat (fun c => Value c .endpoint) := fun _ => "production"
def report : Factory Nat (fun c => Value c .report) := fun c => s!"production:{c/3}"
def parentDefinition : Definition := KeyedPrototype.compose (KeyedPrototype.slot .endpoint address)
  (KeyedPrototype.slot .quota oldQuota)
def childDefinition : Definition := KeyedPrototype.compose
  ⟨Object.recordSlotGen (.inl .report) (fun final _ => do
    let limit ← final.get.lookup (.inl .quota)
    let endpoint ← final.get.lookup (.inl .endpoint)
    return fun c => String.append (endpoint c) (String.append ":" (Nat.repr (limit c).val))), [.report]⟩
  (KeyedPrototype.slot .quota quota)
def allKeys : List Key := [.report, .quota, .endpoint, .quota]
def finalCatalog : Catalog := { lookup := fun key => match key with
  | .inl .quota => some quota | .inl .endpoint => some address
  | .inl .report => some report | .inl .missing => none | .inr () => some allKeys }
def catalog (allow : Bool) (keys : List Key) : Catalog :=
  let definition := KeyedPrototype.compose childDefinition parentDefinition
  let intercepted := { definition with layer := DelayedProto.compose (KeyedPrototype.expose keys) definition.layer }
  intercepted.withKeys allow (Thunk.pure finalCatalog) (Thunk.pure Record.empty)
def render (key : Key) (value : Value context key) : String := match key with
  | .quota => Nat.repr value.val | .endpoint | .report | .missing => value
def flatten {context : Nat} {keys : List Key} (data : Requirements.Results Value context keys) : List String :=
  match keys, data with
  | [], _ => []
  | key :: _, (head, tail) => render key head :: flatten tail
def observations (record : Record Key (Value context)) : Option Nat × Option String × Option String × Bool :=
  ((record.lookup .quota).map Subtype.val, record.lookup .endpoint, record.lookup .report,
    (record.lookup .missing).isSome)

-- The model knows only declaration order and domain formulas. It never uses
-- introspection, descriptors, dependent tuple access or prototype composition.
def expectedExport (context : Nat) : List Key → Except (EnumeratedRequirements.Error Key) (List String)
  | [] => .ok []
  | .missing :: _ => .error (.missing .missing)
  | key :: rest => (expectedExport context rest).map ((match key with
      | .quota => Nat.repr (context/3) | .endpoint => "production"
      | .report => s!"production:{context/3}" | .missing => "unreachable") :: ·)
def expectedObservations (context : Nat) (keys : List Key) :=
  (if keys.contains .quota then some (context/3) else none,
   if keys.contains .endpoint then some "production" else none,
   if keys.contains .report then some s!"production:{context/3}" else none, false)
def checkEnumeration : IO Nat := do
  let mut count := 0
  for allow in [false, true] do
    for keys in [[], [.quota], [.report, .quota], [.report, .quota, .report], [.endpoint, .quota],
        [.missing, .report], [.report, .missing, .quota], [.quota, .report, .missing]] do
      for context in [0, 1, 8, 33] do
        let result := EnumeratedRequirements.prepare (catalog allow keys)
        let requested := if allow then keys else allKeys
        unless (result.map fun ready => flatten (Requirements.build ready.factories context)) == expectedExport context requested do
          throw (IO.userError "declared heterogeneous tuples / duplicate keys / first missing")
        match result with
        | .error _ => pure ()
        | .ok ready =>
          unless ready.keys == requested && observations (ready.buildRecord context) == expectedObservations context requested do
            throw (IO.userError "narrow built interface / final self / key interception")
        count := count+1
  return count

-- Divergence is in function bodies, so preparation must retain them unforced.
private instance : Inhabited Fields := ⟨blank⟩
private instance : Inhabited Catalog := ⟨{ lookup := fun _ => none }⟩
partial def forbidden (_ : Nat) : Nat := forbidden 0
partial def forbiddenLayer (_self _base : Thunk Fields) : Fields := forbiddenLayer _self _base
partial def forbiddenCatalog (_ : Unit) : Catalog := forbiddenCatalog ()
def checkFailures : IO Nat := do
  let unforced ← IO.ofExcept (MetaPrototype.prepareChecked "Unforced"
    (MetadataFamily.constantMetadata forbiddenLayer [] []) [])
  unless unforced.order == ["Unforced"] do throw (IO.userError "preparation applied production")
  let mut count := 1
  for order in [["West"], ["Audit", "Common"], ["West", "Common", "Common"],
      ["West", "missing", "Common"], ["West", "Audit", "Common"], ["Common", "West"]] do
    let poisoned := (registry 1 2).map fun (name, entry) =>
      (name, if name == "West" then parent (west 1) ["Common"] order else entry)
    unless !(MetaPrototype.prepareChecked "Root" (MetadataFamily.constantMetadata forbiddenLayer ["West", "Audit"] []) poisoned).isOk do
      throw (IO.userError "parent cache refusal before production")
    count := count+1
  for supers in [["missing"], ["Root"], ["West", "West"]] do
    unless !(MetaPrototype.prepareChecked "Root" (MetadataFamily.constantMetadata forbiddenLayer supers []) (registry 1 2)).isOk do
      throw (IO.userError "root graph refusal before production")
    count := count+1
  let retained : Catalog := { lookup := fun key => match key with
    | .inr () => some [.quota, .missing, .report]
    | .inl .quota => some quota | .inl .missing => none
    | .inl key => (forbiddenCatalog ()).lookup (.inl key) }
  match EnumeratedRequirements.prepare retained with
  | .error (.missing .missing) => pure ()
  | _ => throw (IO.userError "queried tail after first missing")
  let body : EnumeratedRequirements.Catalog Nat Nat (fun _ _ => Nat) := { lookup := fun key => match key with
    | .inr () => some [0, 0] | .inl _ => some forbidden }
  unless (EnumeratedRequirements.prepare body).isOk do throw (IO.userError "applied retained factory")
  let absent : Catalog := { lookup := fun _ => none }
  match EnumeratedRequirements.prepare absent with
  | .error .missingKeys => pure ()
  | _ => throw (IO.userError "missing declaration differs from empty declaration")
  return count+3

def run : IO Unit := do
  let metadata ← checkMetadata
  let enumeration ← checkEnumeration
  let failures ← checkFailures
  IO.println s!"FUNCTIONAL-REFLECTIVE-REQUIREMENTS-OK metadata={metadata} enumeration={enumeration} refusalsOrUnforced={failures} independentModels=true"
#eval run
end LeanPoo.Tests.FunctionalReflectiveRequirements

#print axioms LeanPoo.Functional.MetadataFamily.constantMetadata_closed
#print axioms LeanPoo.Functional.MetadataFamily.prepareOpen_selected
#print axioms LeanPoo.Functional.MetadataFamily.prepare_source
#print axioms LeanPoo.Functional.MetadataFamily.selected_source
#print axioms LeanPoo.Functional.MetadataFamily.prepare_stable
#print axioms LeanPoo.Functional.MetadataFamily.frozen_order
#print axioms LeanPoo.Functional.EnumeratedRequirements.prepare_source
#print axioms LeanPoo.Functional.EnumeratedRequirements.prepare_missingKeys_iff
#print axioms LeanPoo.Functional.EnumeratedRequirements.prepare_missing_iff
#print axioms LeanPoo.Functional.EnumeratedRequirements.Prepared.producer
#print axioms LeanPoo.Functional.EnumeratedRequirements.Prepared.project_ready
#print axioms LeanPoo.Functional.EnumeratedRequirements.withKeys_source
