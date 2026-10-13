import LeanPoo.Functional.MetadataFamily
import LeanPoo.Functional.ContextPullback

/-! A checked metadata diamond composes first-class capacity and scheduling
factories. Scheduling reads final-self capacity; parent wrappers do not commute.
The declared composition has a slotwise closure proof; checked production is
applied to an explicit final self and retains typed scheduling bounds. -/
namespace LeanPoo.Examples.MetadataDeployment
open Functional Prototype Requirements

inductive Capability where
  | capacity | schedule | owner | missing
  deriving DecidableEq, Repr

structure Schedule (budget : Nat) where
  limit : Nat
  enough : budget ≤ limit
  used : Nat
  fits : used ≤ limit
  bounded : used ≤ budget+4

def Value (budget : Nat) : Capability → Type
  | .capacity => {limit : Nat // budget+4 ≤ limit ∧ limit ≤ budget+10}
  | .schedule | .missing => Schedule budget
  | .owner => String

abbrev Fields := FactoryRecord Nat Capability Value
def base : Fields := Record.empty
def capacity (extra : Nat) (lower : 4 ≤ extra) (upper : extra ≤ 10) : Factory Nat (fun c => Value c .capacity) := fun c => ⟨c+extra, by constructor <;> omega⟩

def common : MetaPrototype.Layer Fields :=
  DelayedProto.compose (Object.recordSlotGen .capacity (fun _ _ => some (capacity 10 (by decide) (by decide))))
    (DelayedProto.compose (Object.recordSlotGen .schedule (fun self _ =>
      (self.get.lookup .capacity).map fun limit => fun c =>
        ⟨(limit c).val, by have := (limit c).property.1; omega,
          min (limit c).val (c+4), Nat.min_le_left _ _, Nat.min_le_right _ _⟩))
      (Object.recordSlotGen .owner (fun _ _ => some (fun _ => "common"))))

def shrink (old : Schedule c) : Schedule c :=
  ⟨old.limit, old.enough, old.used-1, Nat.le_trans (Nat.sub_le _ _) old.fits, Nat.le_trans (Nat.sub_le _ _) old.bounded⟩
def halve (old : Schedule c) : Schedule c :=
  ⟨old.limit, old.enough, old.used/2, Nat.le_trans (Nat.div_le_self _ _) old.fits, Nat.le_trans (Nat.div_le_self _ _) old.bounded⟩

def wrap (change : ∀ c, Schedule c → Schedule c) : MetaPrototype.Layer Fields :=
  Object.recordSlotGen .schedule (fun _ inherited =>
    inherited.get.map (fun factory => Factory.map change factory))

def west : MetaPrototype.Layer Fields :=
  DelayedProto.compose (wrap (fun _ => shrink))
    (Object.recordSlotGen .owner (fun _ _ => some (fun _ => "west")))
def audit : MetaPrototype.Layer Fields :=
  DelayedProto.compose (wrap (fun _ => halve))
    (Object.recordSlotGen .owner (fun _ _ => some (fun _ => "audit")))
def root : MetaPrototype.Layer Fields := Object.recordSlotGen .capacity (fun _ _ => some (capacity 4 (by decide) (by decide)))

def parentInstance (layer : MetaPrototype.Layer Fields) (parents order : List String) : MetaPrototype.Instance Fields :=
  ⟨Thunk.pure base, some (MetadataFamily.constantMetadata layer parents order), fun _ inherited => inherited.get⟩
def registry : MetaPrototype.Registry Fields := [
  ("Common", parentInstance common [] ["Common"]),
  ("West", parentInstance west ["Common"] ["West", "Common"]),
  ("Audit", parentInstance audit ["Common"] ["Audit", "Common"])]

def checked (reverse : Bool) := MetaPrototype.prepareChecked "Deployment"
  (MetadataFamily.constantMetadata root (if reverse then ["Audit", "West"] else ["West", "Audit"]) []) registry

def finalSchedule (reverse : Bool) : Factory Nat (fun c => Value c .schedule) := fun c =>
  let initial : Schedule c := ⟨c+4, by omega, c+4, Nat.le_refl _, Nat.le_refl _⟩
  if reverse then halve (shrink initial) else shrink (halve initial)

def provider (reverse : Bool) : Provider Nat Capability Value
  | .capacity => some (capacity 4 (by decide) (by decide))
  | .schedule => some (finalSchedule reverse)
  | .owner => some (fun _ => if reverse then "audit" else "west")
  | .missing => none

/-- An explicit final-self record supplies the current capacity; source layers
still wrap their inherited schedule in the checked C3 order. -/
def self (reverse : Bool) : Fields := { lookup := provider reverse }

abbrev keys : List Capability := [.schedule, .capacity, .owner]
def Joint (c : Nat) (data : Results Value c keys) : Prop :=
  data.1.used ≤ data.2.1.val

theorem admit (selectedProvider : Provider Nat Capability Value) (factories : Factories Nat Value keys)
    (_selected : Selected selectedProvider keys factories) : ∀ c, Joint c (build factories c) := by
  intro c
  have bounded := (build factories c).1.bounded
  have available := (build factories c).2.1.property.1
  exact Nat.le_trans bounded available

theorem declared_program (reverse : Bool) (key : Capability) :
    ((DelayedProto.composeAll (if reverse then [root, audit, west, common] else [root, west, audit, common]))
      (Thunk.pure (self reverse)) (Thunk.pure base)).lookup key = provider reverse key := by
  cases reverse <;> cases key <;>
    simp [DelayedProto.composeAll, DelayedProto.Chain.ofList, DelayedProto.Chain.toProto,
      DelayedProto.compose, root, audit, west, common, wrap, Object.recordSlotGen,
      self, provider, base, Record.empty, Thunk.get, Thunk.pure,
      capacity, Option.map, DelayedProto.identity]
  all_goals rfl

structure Request where
  budget : Nat
  label : String
structure Receipt (request : Request) where
  used : Nat
  capacity : Nat
  fits : used ≤ capacity
  owner : String
  label : String
def construct (request : Request) (data : Results Value request.budget keys)
    (valid : Joint request.budget data) : Receipt request :=
  ⟨data.1.used, data.2.1.val, valid, data.2.2.1, request.label⟩

def scenario (reverse : Bool) : Except (Sum String Capability) (List (Nat × Nat × String × String × Bool)) := do
  let prepared ← (checked reverse).mapError Sum.inl
  let produced := MetadataFamily.apply prepared (self reverse) base
  let ready ← (prepareCertified produced keys Joint (admit produced)).mapError Sum.inr
  let mut slot := ContextSlot.empty ready
  let mut outputs := []
  for request in [Request.mk 6 "first", ⟨6, "second"⟩, ⟨7, "third"⟩] do
    let (receipt, next, hit) := slot.consumeAlong Request.budget construct request
    slot := next
    outputs := outputs ++ [(receipt.used, receipt.capacity, receipt.owner, receipt.label, hit)]
  return outputs

#guard ((checked false).toOption.map MetaPrototype.Prepared.order) == some ["Deployment", "West", "Audit", "Common"]
#guard ((checked true).toOption.map MetaPrototype.Prepared.order) == some ["Deployment", "Audit", "West", "Common"]
#guard (scenario false).toOption == some [(4, 10, "west", "first", false),
  (4, 10, "west", "second", true), (4, 11, "west", "third", false)]
#guard (scenario true).toOption == some [(4, 10, "audit", "first", false),
  (4, 10, "audit", "second", true), (5, 11, "audit", "third", false)]
#guard (Requirements.prepare (provider false) [.capacity, .missing, .owner]).toOption.isNone
#eval IO.println s!"metadata deployment: {repr (scenario false).toOption}; revised: {repr (scenario true).toOption}"

end LeanPoo.Examples.MetadataDeployment

#print axioms LeanPoo.Examples.MetadataDeployment.declared_program
#print axioms LeanPoo.Examples.MetadataDeployment.admit
