import LeanPoo.Functional.MetadataClosure

namespace LeanPoo.Tests.FunctionalMetadataClosure
open Functional Prototype

abbrev Fields := FactoryRecord Nat String (fun _ _ => Nat)
def reads (mode : Nat) (key : String) : List String :=
  if key = "used" then "capacity" :: (if mode = 1 then ["ghost"] else if mode = 2 then ["report"] else [])
  else if key = "report" then ["used"] else []
abbrev Local (mode : Nat) := MetadataFamily.LayerLocal (Context := Nat) (Value := fun _ _ => Nat) (reads mode)
def constant (key : String) (factory : Nat → Nat) : MetaPrototype.Layer Fields := Object.recordSlotGen key (fun _ _ => some factory)
def forward (key source : String) : MetaPrototype.Layer Fields := Object.recordSlotGen key (fun self _ => self.get.lookup source)
def wrapper (fee scale : Nat) : MetaPrototype.Layer Fields := Object.recordSlotGen "used"
  (fun _ inherited => inherited.get.map fun factory => fun c => factory c * scale + fee)
theorem constant_local (mode : Nat) (key : String) (factory : Nat → Nat) : Local mode (constant key factory) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ _
  rfl
theorem forward_local (mode : Nat) (key source : String) (member : source ∈ reads mode key) : Local mode (forward key source) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight same _
  exact same source member
theorem wrapper_local (mode fee scale : Nat) : Local mode (wrapper fee scale) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ same
  subst oldRight
  rfl
def common : MetaPrototype.Layer Fields := DelayedProto.compose (forward "used" "capacity")
  (DelayedProto.compose (forward "report" "used") (constant "owner" (fun _ => 0)))
theorem common_local (mode : Nat) : Local mode common :=
  MetadataFamily.LayerLocal.compose (forward_local mode _ _ (by simp [reads]))
    (MetadataFamily.LayerLocal.compose (forward_local mode _ _ (by simp [reads])) (constant_local mode _ _))
def west (fee : Nat) : MetaPrototype.Layer Fields := DelayedProto.compose (wrapper fee 1) (constant "owner" (fun _ => 1))
def audit (scale : Nat) : MetaPrototype.Layer Fields := DelayedProto.compose (wrapper 0 scale) (constant "owner" (fun _ => 2))
def parents (mode fee scale : Nat) : List (MetadataFamily.Parent (Context := Nat) (Value := fun _ _ => Nat) (reads mode)) := [
  ⟨"Common", [], ["Common"], common, common_local mode⟩,
  ⟨"West", ["Common"], ["West", "Common"], west fee, MetadataFamily.LayerLocal.compose (wrapper_local _ _ _) (constant_local _ _ _)⟩,
  ⟨"Audit", ["Common"], ["Audit", "Common"], audit scale, MetadataFamily.LayerLocal.compose (wrapper_local _ _ _) (constant_local _ _ _)⟩]
def construct (reverse : Bool) (mode extra fee scale : Nat) :=
  MetadataFamily.prepareClosed "Root" (constant "capacity" (·+extra))
    (if reverse then ["Audit", "West"] else ["West", "Audit"])
    (MetadataFamily.Parent.registry (parents mode fee scale)) (Record.empty : Fields)
    ["report", "used", "owner", "capacity"] (reads mode)
    (by
      intro key dependency member
      by_cases used : key = "used"
      · subst key; simp
      · by_cases report : key = "report"
        · subst key; simp
        · simp [reads, used, report] at member)
    (constant_local _ _ _) (MetadataFamily.Parent.registry_local _)

def flatten {keys : List String} {context : Nat}
    (data : Requirements.Results (fun (_ : Nat) (_ : String) => Nat) context keys) : List Nat :=
  match keys, data with | [], _ => [] | _ :: _, (head, tail) => head :: flatten tail

-- This oracle uses only arithmetic and ordered list lookup. It has no
-- metadata, prototypes, scheduling, selected tuples, or factory evaluation.
def expected (reverse : Bool) (extra fee scale context : Nat) : List String → Except String (List Nat)
  | [] => .ok []
  | key :: rest =>
    let value := if key = "capacity" then some (context+extra)
      else if key = "used" ∨ key = "report" then
        some (if reverse then (context+extra+fee)*scale else (context+extra)*scale+fee)
      else if key = "owner" then some (if reverse then 2 else 1) else none
    match value with | none => .error key | some value => (expected reverse extra fee scale context rest).map (value :: ·)
def equal (left right : Except String (List Nat)) : Bool :=
  match left, right with | .ok a, .ok b => a == b | .error a, .error b => a == b | _, _ => false

def check : IO Unit := do
  let mut count := 0
  for reverse in [false, true] do
    for extra in [0, 4] do
      for fee in [0, 1, 3] do
        for scale in [0, 1, 2] do
          let constructed ← IO.ofExcept ((construct reverse 0 extra fee scale).mapError (fun _ => "automatic closure"))
          unless constructed.plan.order == (if reverse then ["Root", "Audit", "West", "Common"] else ["Root", "West", "Audit", "Common"]) do
            throw (IO.userError "actual checked C3 order")
          for context in [0, 1, 7, 10] do
            for keys in [[], ["report", "used", "capacity", "owner"], ["report", "report"],
                ["unknown", "used"], ["used", "missing", "report"], ["capacity"]] do
              let actual := (constructed.family.prepare keys).map (fun factories => flatten (Requirements.build factories context))
              unless equal actual (expected reverse extra fee scale context keys) do
                throw (IO.userError "closed source factories / first missing / duplicate request")
              count := count+1
  IO.println s!"metadata closure: {count} independent controls"

#eval check
#guard (match construct false 1 4 1 2 with | .error (.inr (.unknownDependency key dependency)) => key == "used" && dependency == "ghost" | _ => false)
#guard (match construct false 2 4 1 2 with | .error (.inr (.blocked remaining)) => remaining == ["report", "used"] | _ => false)
#print axioms MetadataFamily.Dependencies.close_unique
#print axioms MetaPrototype.prepareChecked_origin
#print axioms MetaPrototype.Prepared.program_property
end LeanPoo.Tests.FunctionalMetadataClosure
