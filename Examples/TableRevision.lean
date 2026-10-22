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

/-- Explicitly change the key type without inferring an isomorphism. -/
def serviceKeys : Prototype.DictionaryBridge Nat (Nat × Unit) :=
  ⟨fun key => (key, ()), Prod.fst, fun _ => rfl, fun pair => by cases pair; rfl⟩

/-- Reorder an opaque callback handle and its flag, preserving handle identity.
The model intentionally does not decide extensional equality of procedures. -/
def serviceValues : Prototype.DictionaryBridge (Nat × Bool) (Bool × Nat) :=
  ⟨Prod.swap, Prod.swap, fun _ => rfl, fun _ => rfl⟩

/-- Two services share a callback handle; the revision moves one service and
changes its flag while leaving the other handle unchanged. -/
def callbackLedger (key : Nat) : Option (Nat × Bool) :=
  if key = 1 ∨ key = 9 then some (41, false) else none

/-- Ordered deletion and insertion retain the shared admitted callback handle. -/
def callbackEdits : List (Change Nat (Nat × Bool)) :=
  [⟨1, some (41, false), none⟩, ⟨3, none, some (41, true)⟩]

/-- The general theorem covers every key and maps the exact refusal key. -/
example : applyChanges (transportChanges serviceKeys serviceValues callbackEdits)
      (transportView serviceKeys serviceValues callbackLedger) =
    ((applyChanges callbackEdits callbackLedger).mapError serviceKeys.toFields).map
      (transportView serviceKeys serviceValues) :=
  transport_applyChanges serviceKeys serviceValues callbackEdits callbackLedger

example : transportView serviceKeys serviceValues callbackLedger (9, ()) = some (false, 41) := by rfl

example : transportChanges serviceKeys.inverse serviceValues.inverse
    (transportChanges serviceKeys serviceValues callbackEdits) = callbackEdits :=
  transportChanges_inverse serviceKeys serviceValues callbackEdits

/-- A competing edit fails at the converted key; no successful prefix is returned. -/
example : (applyChanges (transportChanges serviceKeys serviceValues callbackEdits)
    (transportView serviceKeys serviceValues (replace callbackLedger 1 none))).map
      (fun view => view (3, ())) = .error (1, ()) := by rfl

/-- Finite negative control: a collapsing key map cannot satisfy the inverse law. -/
example : ¬ ∃ inverse : Nat → Nat, ∀ key : Nat, inverse (key % 2) = key := by
  rintro ⟨inverse, law⟩
  have zero := law 0
  have two := law 2
  simp only [Nat.zero_mod, Nat.mod_self] at zero two
  omega

/-- Count enabled callback capacity with an exact key-dependent integer score.
The opaque callback handle is read as data; folding never invokes a callback. -/
def capacityScore (key : Nat) (payload : Nat × Bool) : Int :=
  if payload.2 then Int.ofNat (key * payload.1) else 0

/-- Delete one disabled service and insert an enabled service, sharing handle 41. -/
example : (applyFold capacityScore callbackEdits callbackLedger
    (foldView [1,3,9] capacityScore callbackLedger)).map Prod.snd = .ok 123 := by rfl

/-- Every successful full workflow agrees with its complete finite reference fold. -/
example : applyFold capacityScore callbackEdits callbackLedger
      (foldView [1,3,9] capacityScore callbackLedger) =
    (applyChanges callbackEdits callbackLedger).map
      (fun after => (after, foldView [1,3,9] capacityScore after)) := by
  apply applyFold_correct [1,3,9] (by decide)
  intro edit member
  simp [callbackEdits] at member
  rcases member with rfl | rfl <;> decide

/-- Inverse edits restore the original accumulator, including an unrelated offset. -/
example : foldChanges capacityScore (inverseChanges callbackEdits)
    (foldChanges capacityScore callbackEdits 700) = 700 :=
  foldChanges_inverse capacityScore callbackEdits 700

/-- Moving both keys and callback payload layout preserves source and aggregate,
including errors, by the general isomorphism theorem. -/
example : applyFold (transportScore serviceKeys serviceValues capacityScore)
      (transportChanges serviceKeys serviceValues callbackEdits)
      (transportView serviceKeys serviceValues callbackLedger) 0 =
    ((applyFold capacityScore callbackEdits callbackLedger 0).mapError serviceKeys.toFields).map
      (fun result => (transportView serviceKeys serviceValues result.1, result.2)) :=
  transport_applyFold serviceKeys serviceValues capacityScore callbackEdits callbackLedger 0

/-- A competing callback handle refuses before any aggregate is returned. -/
def callbackWinner : Nat → Option (Nat × Bool) := replace callbackLedger 1 (some (42, false))

example : (applyFold capacityScore callbackEdits callbackWinner 0).map Prod.snd = .error 1 := by rfl

/-- Rediscover against the winning snapshot, then retry the complete operation. -/
def callbackTarget : Nat → Option (Nat × Bool) :=
  replace (replace callbackLedger 1 none) 3 (some (41, true))

example : (applyFold capacityScore (diffChanges [1,3,9] callbackWinner callbackTarget)
    callbackWinner (foldView [1,3,9] capacityScore callbackWinner)).map Prod.snd = .ok 123 := by rfl

/-- This delete/insert delta projects exactly two payloads; no full fold occurs. -/
example : foldWork callbackEdits = 2 := by rfl

/-- Sparse target replay reuses the source fold; the paired-view invariant makes
it observationally identical to full target execution, including failure keys. -/
example : reuseFold serviceKeys serviceValues capacityScore callbackEdits callbackLedger
      (transportView serviceKeys serviceValues callbackLedger) 0 =
    applyFold (transportScore serviceKeys serviceValues capacityScore)
      (transportChanges serviceKeys serviceValues callbackEdits)
      (transportView serviceKeys serviceValues callbackLedger) 0 :=
  reuseFold_correct serviceKeys serviceValues capacityScore callbackEdits callbackLedger _ rfl 0

example : (reuseFold serviceKeys serviceValues capacityScore callbackEdits callbackWinner
    (transportView serviceKeys serviceValues callbackWinner) 0).map Prod.snd = .error (1, ()) := by rfl

/-- A source already paired with a target retains its exact aggregate on recovery. -/
example : (transportView serviceKeys.inverse serviceValues.inverse
    (transportView serviceKeys serviceValues callbackLedger), (700 : Int)) = (callbackLedger, 700) :=
  retained_fold_inverse serviceKeys serviceValues callbackLedger 700

/-- Metadata 0 is source, 1 converter, and 2 aggregate: only converter changes. -/
def originalStamps (_ : Nat) : Option Nat := some 0

def converterEdit : List (Change Nat Nat) := [⟨1, some 0, some 1⟩]

example : ∀ key ∈ [0,2], replace originalStamps 1 (some 1) key = originalStamps key := by
  apply fold_dependency_frame converterEdit originalStamps _ (by rfl) [0,2]
  intro edit member
  simp only [converterEdit, List.mem_singleton] at member
  subst edit
  decide

example : replace originalStamps 1 (some 1) 1 ≠ originalStamps 1 :=
  fold_dependency_changed originalStamps 1 0 1 rfl (by decide)

/-- Only source projections are needed: two in this delete/insert example,
zero target projections and zero complete conversion scans on the paired path. -/
example : reuseFoldWork callbackEdits = (2,0,0) := rfl

/-- Shared source/aggregate stamps can be prepared once without losing refusal. -/
example : prepareStamped [0,0,2] originalStamps originalStamps (7 : Int) = .ok 7 := rfl

example : prepareStamped [0,1,0,2] originalStamps
    (replace originalStamps 1 (some 1)) (7 : Int) = .error () := rfl

example : (do let _ ← prepareStamped [0,1] originalStamps originalStamps ()
              prepareStamped [0,2] originalStamps originalStamps (7 : Int)) =
    prepareStamped ([0,1] ++ [0,2]).eraseDups originalStamps originalStamps 7 :=
  prepareStamped_fuse [0,1] [0,2] originalStamps originalStamps 7

/-- Exact sharing and empty outer scopes retain their existing guard lists. -/
example : extendProtection ([0,1,2] : List Nat) [0,1,2] true = [0,1,2] := rfl
example : extendProtection ([0,3,2] : List Nat) [] false = [0,3,2] := rfl

/-- Partial overlaps keep their complete original protection without searching. -/
example : extendProtection ([0,3,2] : List Nat) [0,1,2] false = [0,3,2,0,1,2] := rfl

/-- A changed new origin remains rejected by the constant-time scope selection. -/
example : stampMatches (extendProtection [0,3,2] [0,1,2] false) originalStamps
    (replace originalStamps 3 (some 1)) = false := rfl

#print axioms stampMatches_extendProtection
#print axioms extendProtection_shared
#print axioms extendProtection_length_le

#print axioms prepareStamped_fuse
#print axioms stampMatches_dedup

#print axioms reuseFold_correct
#print axioms retained_fold_inverse
#print axioms fold_dependency_frame
#print axioms reuseFoldWork_bound

#print axioms foldChanges_correct
#print axioms applyFold_correct
#print axioms foldChanges_inverse
#print axioms transport_applyFold
#print axioms foldWork_bound

#print axioms transport_applyChanges
#print axioms transportView_inverse
#print axioms applyChanges_inverse
#print axioms diff_complete
#print axioms transport_changes
end LeanPoo.Examples.TableRevision
