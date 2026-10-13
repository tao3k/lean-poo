import LeanPoo.Functional.FactoryDispatchPublication
import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.SimplePolicies

/-! Upgrade a noncommuting C3 factory diamond together with pricing plugins.
Negative Bank assumptions and actual Card prices are checked before publishing.
Refused construction, extension or joint admission retains the old warm version. -/
namespace LeanPoo.Examples.JointPublication
open Functional Prototype Requirements Object Object.MethodCombination
open Functional.DispatchExtension Functional.FactoryDispatchPublication

inductive Key where
  | rate | total | capacity
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr
abbrev Value (_ : Nat) (_ : Key) := Nat
abbrev Fields := FactoryRecord Nat Key Value
def base : Fields := Record.empty
def reads : Key → List Key | .total => [.rate] | _ => []
abbrev Local := MetadataFamily.LayerLocal (Context := Nat) (Value := Value) reads
def common : MetaPrototype.Layer Fields := Object.recordSlotGen .rate (fun _ _ => some (fun c => c+2))
def wrap (f : Nat → Nat) : MetaPrototype.Layer Fields :=
  Object.recordSlotGen .rate (fun _ inherited => inherited.get.map (fun rate c => f (rate c)))
def root : MetaPrototype.Layer Fields := DelayedProto.compose
  (Object.recordSlotGen .total (fun self _ => (self.get.lookup .rate).map (fun rate (c : Nat) => (rate c : Nat)+3)))
  (Object.recordSlotGen .capacity (fun _ _ => some (fun c => 2*c+10)))
theorem common_local : Local common := by
  apply MetadataFamily.LayerLocal.slot; intros; rfl
theorem wrap_local (f : Nat → Nat) : Local (wrap f) := by
  apply MetadataFamily.LayerLocal.slot
  intro left right oldLeft oldRight _ same
  simp only [Thunk.get, Thunk.pure]; rw [same]
theorem root_local : Local root := by
  apply MetadataFamily.LayerLocal.compose
  · apply MetadataFamily.LayerLocal.slot
    intro left right oldLeft oldRight same _
    simp only [Thunk.get, Thunk.pure]
    rw [same .rate (by simp [reads])]
  · apply MetadataFamily.LayerLocal.slot; intros; rfl
def parents : List (MetadataFamily.Parent (Context := Nat) (Value := Value) reads) := [
  ⟨"Common", [], ["Common"], common, common_local⟩,
  ⟨"Double", ["Common"], ["Double", "Common"], wrap (2*·), wrap_local _⟩,
  ⟨"Extra", ["Common"], ["Extra", "Common"], wrap (·+1), wrap_local _⟩]
def closeParents (supers : List String) := MetadataFamily.prepareClosed "Pricing" root
  supers
  (MetadataFamily.Parent.registry parents) base [.rate, .total, .capacity] reads
  (by intro key dependency member; cases key <;> simp_all [reads]) root_local (MetadataFamily.Parent.registry_local parents)

def close (reverse : Bool) := closeParents (if reverse then ["Extra", "Double"] else ["Double", "Extra"])

structure Request where
  channel : String
  amount : Nat
abbrev Action := EStateM String (List String)
abbrev Fragment := SimpleContribution Request Action Nat Nat
abbrev Generic := Multimethod Request Fragment (Action Nat)
def shape (request : Request) := [["Retail", "Account"], [request.channel, "Channel"]]
def path (account channel : String) : List Specializer := [.prototype account, .prototype channel]
def initial : Generic := Multimethod.simple 2 shape (SimplePolicy.sum Nat)
def item (name : String) (price : Nat → Nat) : Fragment := .item fun request => do
  modify (· ++ [name]); return price request.amount
def edits (reverse mismatch : Bool) : List (Edit Request Fragment) := [
  .register (path "Account" "Card") (item "rate" (fun c => 2*c+(if reverse then 5 else 6))),
  .register (path "Retail" "Card") (item "fee" (fun _ => if mismatch then 30 else 3))]
def watches : List (Watch Request) := [.shape (shape ⟨"Bank", 0⟩)]
def observe (generic : Generic) : Except String (Nat × List String) := do
  let (action, _) ← (generic.call ⟨"Card", 5⟩).mapError (fun _ => "shape")
  match action.run ["request"] with
  | .ok price ledger => .ok (price, ledger)
  | .error error _ => .error error

structure Approval (construction : MetadataFamily.Construction base) (generic : Generic) where
  factories : Requirements.Factories Nat Value [.total, .capacity]
  selected : Selected construction.family.provider [.total, .capacity] factories
  receipt : Nat × List String
  observed : observe generic = .ok receipt
  agrees : receipt.1 = (build factories 5).1
  fits : receipt.1 ≤ (build factories 5).2.1

def admit (construction : MetadataFamily.Construction base) (generic : Generic) : Except String (Approval construction generic) :=
  match prepared : prepare construction.family.provider [.total, .capacity] with
  | .error _ => .error "missing factory"
  | .ok factories => match observed : observe generic with
    | .error error => .error error
    | .ok receipt =>
      if agrees : receipt.1 = (build factories 5).1 then
        if fits : receipt.1 ≤ (build factories 5).2.1 then
          .ok ⟨factories, (prepare_ok_iff _ _ _).mp prepared, receipt, observed, agrees, fits⟩
        else .error "capacity"
      else .error "factory/dispatch disagreement"

abbrev Version := Snapshot base watches Approval
def start : Except String Version := do
  let factories ← (close false).mapError (fun _ => "construction")
  let generic ← (patch initial (edits false false)).mapError (fun _ => "registration")
  let (_, warm) ← (generic.call ⟨"Card", 5⟩).mapError (fun _ => "warm")
  let negative ← (check warm watches).mapError (fun _ => "negative")
  let approval ← admit factories warm
  return ⟨factories, warm, negative, approval⟩

def summary (version : Version) : List String :=
  version.factories.plan.order ++ [s!"price:{version.approval.receipt.1}", s!"cache:{version.generic.cache.values.size}"]
def scenario : Except String (List (List String)) := do
  let old ← start
  let (accepted, revised) := publish old (fun _ => close true) (edits true false) admit
  if accepted.toOption.isNone then throw "upgrade"
  let (_, mismatch) := publish old (fun _ => close true) (edits true true) admit
  let (_, conflict) := publish old (fun _ => close true)
    (edits true false ++ [.register (path "Account" "Bank") (item "orphan" (fun _ => 1))]) admit
  let (_, missing) := publish old (fun _ => closeParents ["Missing"]) (edits true false) admit
  return [summary old, summary revised, summary mismatch, summary conflict, summary missing]

#guard scenario.toOption == some [
  ["Pricing", "Double", "Extra", "Common", "price:19", "cache:1"],
  ["Pricing", "Extra", "Double", "Common", "price:18", "cache:0"],
  ["Pricing", "Double", "Extra", "Common", "price:19", "cache:1"],
  ["Pricing", "Double", "Extra", "Common", "price:19", "cache:1"],
  ["Pricing", "Double", "Extra", "Common", "price:19", "cache:1"]]

-- The proof is attached to both exact selected factories and actual dispatch.
theorem published_price_fits (version : Version) :
    version.approval.receipt.1 ≤ (build version.approval.factories 5).2.1 := version.approval.fits
#print axioms Functional.FactoryDispatchPublication.publish_refused
#print axioms Functional.FactoryDispatchPublication.Revision.cacheSound
#print axioms Snapshot.closed
#print axioms published_price_fits
end LeanPoo.Examples.JointPublication
