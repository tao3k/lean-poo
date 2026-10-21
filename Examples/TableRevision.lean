import LeanPoo.Functional.TableRevision

/-! Portable service-ledger revisions with false values, deletion, retry and
nested optional focus. Gerbil supplies paired RationalDict/Trie regression tests. -/
namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- A shared service ledger before deletion and false-valued insertion. -/
def original (key : Nat) : Option Bool :=
  if key = 1 then some false else if key = 2 ∨ key = 9 then some true else none

/-- The next ledger changes keys 1, 2 and 3, retaining shared service 9. -/
def proposed (key : Nat) : Option Bool :=
  if key = 1 ∨ key = 9 then some true else if key = 3 then some false else none

/-- The finite union of both live domains determines discovery. -/
def delta : List (Change Nat Bool) := diffChanges [1,2,3,9] original proposed

example : delta.length = 3 := by decide

/-- Complete discovery reconstructs the target at every key, not just sample keys. -/
theorem installed : applyChanges delta original = .ok proposed := by
  apply diff_complete [1,2,3,9] (by decide)
  intro key outside
  simp only [List.mem_cons, not_or] at outside
  simp [original, proposed, outside.1, outside.2.1, outside.2.2.1, outside.2.2.2]

/-- Inverting a completed revision preserves all original observations. -/
example : applyChanges (inverseChanges delta) proposed = .ok original :=
  applyChanges_inverse delta original proposed installed

/-- A concurrent change conflicts after the privately staged first edit. -/
def winner : Nat → Option Bool := replace original 2 (some false)
example : (applyChanges delta winner).map (fun view => view 1) = .error 2 := by rfl

/-- Rediscovery against the winner permits a fresh successful retry. -/
example : (applyChanges (diffChanges [1,2,3,9] winner proposed) winner).map
    (fun view => (view 1, view 2, view 3, view 9)) =
    .ok (some true, none, some false, some true) := by rfl

/-- A table embedded in a service keeps unrelated metadata on persistent writes. -/
def serviceCarrier : TableCarrier Nat Bool ((Nat → Option Bool) × String) where
  read := Prod.fst
  write := fun source key value => (replace source.1 key value, source.2)
  read_write := fun _ _ _ => rfl

/-- The plain observation carrier is another representation of the same ledger. -/
def viewCarrier : TableCarrier Nat Bool (Nat → Option Bool) where
  read := id
  write := replace
  read_write := fun _ _ _ => rfl

/-- Same-view carriers share deltas, successes and conflicts without conversion
of their internal tree shape or metadata. This uses the general transport proof. -/
example : (serviceCarrier.apply delta (original,"billing")).map serviceCarrier.read =
    (viewCarrier.apply delta original).map viewCarrier.read :=
  transport_changes serviceCarrier viewCarrier delta (original,"billing") original rfl

example : (serviceCarrier.apply delta (original,"billing")).map Prod.snd = .ok "billing" := by rfl

/-- Compose a service focus with a total optional-key focus, using existing laws. -/
example : Prototype.LensLaws
    (fun service : (Nat → Option Bool) × String => service.1 3)
    (fun value service => (replace service.1 3 value, service.2)) :=
  Prototype.LensLaws.productFirst.compose (optional_lens 3)

#print axioms applyChanges_inverse
#print axioms diff_complete
#print axioms transport_changes
end LeanPoo.Examples.TableRevision
