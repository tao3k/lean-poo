import LeanPoo.Functional.MetadataClosure
import LeanPoo.Functional.ContextPullback

/-! Automatically close a checked C3 diamond of dependent scheduling factories.
Parent wrappers do not commute; final-self capacity, certified result bounds
and request-specific presentation compose with retained context data. -/
namespace LeanPoo.Examples.ClosedDeployment
open Functional Prototype Requirements

inductive Capability where
  | capacity | schedule | owner | report | missing
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr

structure Schedule (budget : Nat) where
  limit : Nat
  enough : budget ≤ limit
  used : Nat
  fits : used ≤ limit
  bounded : used ≤ budget+4

def Value (budget : Nat) : Capability → Type
  | .capacity => {limit : Nat // budget+4 ≤ limit ∧ limit ≤ budget+10}
  | .schedule | .missing => Schedule budget
  | .owner | .report => String

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
def root : MetaPrototype.Layer Fields := DelayedProto.compose
  (Object.recordSlotGen .capacity (fun _ _ => some (capacity 4 (by decide) (by decide))))
  (Object.recordSlotGen .report (fun self _ => do
    let schedule ← self.get.lookup .schedule
    let owner ← self.get.lookup .owner
    return fun (c : Nat) => String.append (owner c) s!":{(schedule c).used}/{(schedule c).limit}"))

def reads : Capability → List Capability
  | .schedule => [.capacity]
  | .report => [.schedule, .owner]
  | _ => []
abbrev Local := MetadataFamily.LayerLocal (Context := Nat) (Value := Value) reads

theorem capacity_local (extra : Nat) (lower : 4 ≤ extra) (upper : extra ≤ 10) :
    Local (Object.recordSlotGen .capacity (fun _ _ => some (capacity extra lower upper))) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ _
  rfl

theorem owner_local (name : String) :
    Local (Object.recordSlotGen .owner (fun _ _ => some (fun _ => name))) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ _
  rfl

theorem common_local : Local common := by
  apply MetadataFamily.LayerLocal.compose (capacity_local 10 (by decide) (by decide))
  apply MetadataFamily.LayerLocal.compose
  · apply MetadataFamily.LayerLocal.slot
    intro left right oldLeft oldRight same _
    have selected := same .capacity (by simp [reads])
    simp only [Thunk.get, Thunk.pure]
    rw [selected]
  · exact owner_local "common"

theorem wrap_local (change : ∀ c, Schedule c → Schedule c) : Local (wrap change) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ same
  subst oldRight
  rfl

theorem west_local : Local west := MetadataFamily.LayerLocal.compose (wrap_local _) (owner_local "west")
theorem audit_local : Local audit := MetadataFamily.LayerLocal.compose (wrap_local _) (owner_local "audit")
theorem root_local : Local root := by
  apply MetadataFamily.LayerLocal.compose (capacity_local 4 (by decide) (by decide))
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight same _
  have schedule := same .schedule (by simp [reads])
  have owner := same .owner (by simp [reads])
  simp only [Thunk.get, Thunk.pure]
  rw [schedule, owner]

def annotated : List (MetadataFamily.Parent (Context := Nat) (Value := Value) reads) := [
  ⟨"Common", [], ["Common"], common, common_local⟩,
  ⟨"West", ["Common"], ["West", "Common"], west, west_local⟩,
  ⟨"Audit", ["Common"], ["Audit", "Common"], audit, audit_local⟩]

def close (reverse : Bool) := MetadataFamily.prepareClosed "Deployment" root
  (if reverse then ["Audit", "West"] else ["West", "Audit"])
  (MetadataFamily.Parent.registry annotated) base [.report, .schedule, .capacity, .owner, .missing] reads
  (by intro key dependency member; cases key <;> simp_all [reads])
  root_local (MetadataFamily.Parent.registry_local annotated)

/-- Uniqueness concerns every factory function at every key, rather than
only the finitely executed deployment requests. -/
theorem closed_unique (construction : MetadataFamily.Construction base)
    (other : MetadataFamily construction.plan base) (key : Capability) :
    other.provider key = construction.family.provider key := construction.scheduled.unique other key

abbrev keys : List Capability := [.schedule, .capacity, .owner, .report]
def Joint (c : Nat) (data : Results Value c keys) : Prop :=
  data.1.used ≤ data.2.1.val

theorem admit (selectedProvider : Provider Nat Capability Value) (factories : Factories Nat Value keys)
    (_selected : Selected selectedProvider keys factories) : ∀ c, Joint c (build factories c) := by
  intro c
  have bounded := (build factories c).1.bounded
  have available := (build factories c).2.1.property.1
  exact Nat.le_trans bounded available

structure Request where
  budget : Nat
  label : String
structure Receipt (request : Request) where
  used : Nat
  capacity : Nat
  fits : used ≤ capacity
  owner : String
  label : String
  summary : String
def construct (request : Request) (data : Results Value request.budget keys)
    (valid : Joint request.budget data) : Receipt request :=
  ⟨data.1.used, data.2.1.val, valid, data.2.2.1, request.label, data.2.2.2.1⟩

def scenario (reverse : Bool) : Except (Sum String Capability) (List (Nat × Nat × String × String × String × Bool)) := do
  let construction ← (close reverse).mapError (fun _ => Sum.inl "construction refused")
  let produced := construction.family.provider
  let ready ← (prepareCertified produced keys Joint (admit produced)).mapError Sum.inr
  let mut slot := ContextSlot.empty ready
  let mut outputs := []
  for request in [Request.mk 6 "first", ⟨6, "second"⟩, ⟨7, "third"⟩] do
    let (receipt, next, hit) := slot.consumeAlong Request.budget construct request
    slot := next
    outputs := outputs ++ [(receipt.used, receipt.capacity, receipt.owner, receipt.summary, receipt.label, hit)]
  return outputs

#guard ((close false).toOption.map (fun c => c.plan.order)) == some ["Deployment", "West", "Audit", "Common"]
#guard ((close true).toOption.map (fun c => c.plan.order)) == some ["Deployment", "Audit", "West", "Common"]
#guard (scenario false).toOption == some [(4, 10, "west", "west:4/10", "first", false),
  (4, 10, "west", "west:4/10", "second", true), (4, 11, "west", "west:4/11", "third", false)]
#guard (scenario true).toOption == some [(4, 10, "audit", "audit:4/10", "first", false),
  (4, 10, "audit", "audit:4/10", "second", true), (5, 11, "audit", "audit:5/11", "third", false)]
#guard (close false).toOption.isSome
#guard ((close false).toOption.map (fun c => (c.family.prepare [.capacity, .missing, .owner]).toOption.isNone)) == some true
#eval IO.println s!"metadata deployment: {repr (scenario false).toOption}; revised: {repr (scenario true).toOption}"

end LeanPoo.Examples.ClosedDeployment

#print axioms LeanPoo.Examples.ClosedDeployment.closed_unique
#print axioms LeanPoo.Examples.ClosedDeployment.admit

#print axioms LeanPoo.Functional.MetadataFamily.prepareClosed
#print axioms LeanPoo.Prototype.RankedResolver.unique
