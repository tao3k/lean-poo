import LeanPoo.Functional.FactoryDispatchPublication

/-! Independent arithmetic/phase oracle for complete immutable publication.
Exercises actual metadata construction, first dispatch errors, canceled edits,
joint disagreement/capacity refusal, and cold/warm old-version retention. -/
namespace LeanPoo.Tests.FactoryDispatchPublication
open Functional Prototype Requirements Object Functional.DispatchExtension
open Functional.FactoryDispatchPublication
inductive Key where
  | rate | total | capacity
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Value (_ : Nat) (_ : Key) := Nat
abbrev Fields := FactoryRecord Nat Key Value
def base : Fields := Record.empty
def reads : Key → List Key | .total => [.rate] | _ => []
abbrev Local := MetadataFamily.LayerLocal (Context := Nat) (Value := Value) reads
def parent (extra : Nat) : MetaPrototype.Layer Fields := Object.recordSlotGen .rate (fun _ _ => some (fun c => c+extra))
def root (limit : Nat) : MetaPrototype.Layer Fields := DelayedProto.compose
  (Object.recordSlotGen .total (fun self _ => (self.get.lookup .rate).map (fun rate (c : Nat) => rate c+1)))
  (Object.recordSlotGen .capacity (fun _ _ => some (fun c => c+limit)))
theorem parent_local (extra : Nat) : Local (parent extra) := by
  apply MetadataFamily.LayerLocal.slot; intros; rfl
theorem root_local (limit : Nat) : Local (root limit) := by
  apply MetadataFamily.LayerLocal.compose
  · apply MetadataFamily.LayerLocal.slot
    intro left right oldLeft oldRight same _
    simp only [Thunk.get, Thunk.pure]; rw [same .rate (by simp [reads])]
  · apply MetadataFamily.LayerLocal.slot; intros; rfl
def close (extra limit : Nat) (missing : Bool) :=
  let parents : List (MetadataFamily.Parent (Context := Nat) (Value := Value) reads) :=
    [⟨"Common", [], ["Common"], parent extra, parent_local extra⟩]
  MetadataFamily.prepareClosed "Price" (root limit) [if missing then "Missing" else "Common"]
    (MetadataFamily.Parent.registry parents) base [.rate,.total,.capacity] reads
    (by intro key dependency member; cases key <;> simp_all [reads]) (root_local limit) (MetadataFamily.Parent.registry_local parents)

abbrev Generic := Multimethod Nat Nat Nat
def initial : Generic := { arity := 1, precedence := fun _ => [["Card"]], combine := fun methods amount => methods.foldl (·+·) amount }
def watches : List (Watch Nat) := [.shape [["Bank"]]]
def price (generic : Generic) := (generic.call 5).toOption.map Prod.fst
structure Approval (construction : MetadataFamily.Construction base) (generic : Generic) where
  factories : Requirements.Factories Nat Value [.total,.capacity]
  selected : Selected construction.family.provider [.total,.capacity] factories
  agrees : price generic = some ((build factories 5).1)
  fits : (build factories 5).1 ≤ (build factories 5).2.1
def admit (construction : MetadataFamily.Construction base) (generic : Generic) : Except String (Approval construction generic) :=
  match prepared : prepare construction.family.provider [.total,.capacity] with
  | .error _ => .error "missing"
  | .ok factories =>
    if agrees : price generic = some ((build factories 5).1) then
      if fits : (build factories 5).1 ≤ (build factories 5).2.1 then
        .ok ⟨factories, (prepare_ok_iff _ _ _).mp prepared, agrees, fits⟩
      else .error "capacity"
    else .error "disagreement"
abbrev Version := Snapshot base watches Approval
def start (extra : Nat) (warm : Bool) : Except String Version := do
  let factories ← (close extra (extra+4) false).mapError (fun _ => "close")
  let registered ← (initial.register [.prototype "Card"] (extra+1)).mapError (fun _ => "register")
  let generic ← if warm then (registered.call 5).map Prod.snd |>.mapError (fun _ => "call") else .ok registered
  let negative ← (check generic watches).mapError (fun _ => "check")
  let approved ← admit factories generic
  return ⟨factories, generic, negative, approved⟩

def bit (flags index : Nat) : Bool := flags / 2^index % 2 == 1
def describe {old : Version} {edits : List (Edit Nat Nat)}
    (failure : Failure (FactoryError := Sum String (DependencyError Key)) (AdmissionError := String) old edits) : String :=
  match failure with
  | .construction _ => "construction"
  | .dispatch (.registration _ _) => "arity"
  | .dispatch (.introduced _ _ _) => "negative"
  | .admission _ _ error => error
def actual (oldExtra newExtra flags : Nat) (warm cancel : Bool) : Except String (String × Nat × Option Nat × Nat) := do
  let old ← start oldExtra warm
  let changes : List (Edit Nat Nat) := [.register [.prototype "Card"] (newExtra+1+(if bit flags 3 then 2 else 0))] ++
    (if bit flags 2 then [.register [.prototype "Bank"] 9] else []) ++
    (if cancel then [.erase [.prototype "Bank"]] else []) ++
    (if bit flags 1 then [.register [] 0] else [])
  let (outcome, version) := publish old
    (fun _ => close newExtra (newExtra+(if bit flags 4 then 0 else 4)) (bit flags 0)) changes admit
  let phase := match outcome with | .ok _ => "accepted" | .error failure => describe failure
  return (phase, version.approval.factories.1 5, price version.generic, version.generic.cache.values.size)
def expected (oldExtra newExtra flags : Nat) (warm cancel : Bool) : String × Nat × Option Nat × Nat :=
  let phase := if bit flags 0 then "construction" else if bit flags 1 then "arity"
    else if bit flags 2 && !cancel then "negative" else if bit flags 3 then "disagreement"
    else if bit flags 4 then "capacity" else "accepted"
  let accepted := phase == "accepted"
  let value := 5 + (if accepted then newExtra else oldExtra) + 1
  (phase, value, some value, if accepted then 0 else if warm then 1 else 0)
def cases := [1,3].flatMap fun old => [1,3].flatMap fun new => (List.range 32).flatMap fun flags =>
  [false,true].flatMap fun warm => [false,true].map fun cancel => (old,new,flags,warm,cancel)
#guard cases.length == 512
#guard cases.all fun (old,new,flags,warm,cancel) =>
  (actual old new flags warm cancel).toOption == some (expected old new flags warm cancel)
#print axioms Functional.FactoryDispatchPublication.publish_refused
#print axioms Functional.FactoryDispatchPublication.publish_accepted
#print axioms Functional.FactoryDispatchPublication.Revision.cacheSound
#print axioms Functional.FactoryDispatchPublication.Snapshot.closed
end LeanPoo.Tests.FactoryDispatchPublication
