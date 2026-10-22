import LeanPoo.Functional.TableRepresentation

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

/-- Interface labels may differ while retaining exactly the producer stamps. -/
example : prepareStamped [100,101,102]
    (fun key => originalStamps (key - 100)) (fun key => originalStamps (key - 100)) (9 : Int) =
    prepareStamped [0,1,2] originalStamps originalStamps 9 := by
  exact prepareStamped_transport [0,1,2] (fun key => key + 100) originalStamps originalStamps
    (fun key => originalStamps (key - 100)) (fun key => originalStamps (key - 100))
    (by intro key _; simp) (by intro key _; simp) 9

/-- Old interfaces can still match themselves; producer refusal must prevail. -/
example : prepareStamped [100,101] originalStamps originalStamps (9 : Int) = .ok 9 := rfl
example : (do let _ ← prepareStamped [0,1] originalStamps
                (replace originalStamps 1 (some 1)) ()
              prepareStamped [100,101] originalStamps originalStamps (9 : Int)) = .error () := rfl

/-- A large facade keeps its complete module stamp with one grouped import. -/
example : prepareStamped [0] originalStamps originalStamps (9 : Int) =
    prepareStamped (bindingDependencies [(0,1453)]) originalStamps originalStamps 9 := by
  exact prepareStamped_grouped [(0,1453)] (by intro entry inside; simp at inside; subst entry; decide)
    originalStamps originalStamps 9

/-- A changed facade refuses even when every retained binding is callable. -/
example : prepareStamped [0] originalStamps (replace originalStamps 0 (some 1)) (9 : Int) =
    .error () := rfl

/-- An empty group would silently omit a stale stamp; positivity is essential. -/
example : stampMatches (bindingDependencies [(0,0)]) originalStamps
    (replace originalStamps 0 (some 1)) = true ∧
    stampMatches [0] originalStamps (replace originalStamps 0 (some 1)) = false := by decide

/-- Existing metadata/dispatch facades retain ten inspections instead of 82,
including one complete module stamp for each selected import boundary. -/
example : prepareStamped (bindingDependencies [(0,8),(1,2)]) originalStamps
    (replace originalStamps 1 (some 1)) (9 : Int) =
    prepareStamped (bindingDependencies [(0,44),(1,38)]) originalStamps
      (replace originalStamps 1 (some 1)) 9 := by
  apply prepareStamped_regroup
  · intro entry inside; simp at inside
    rcases inside with rfl | rfl <;> decide
  · intro entry inside; simp at inside
    rcases inside with rfl | rfl <;> decide
  · rfl

example : (bindingDependencies ([(0,8),(1,2)] : List (Nat × Nat))).length = 10 ∧
    (bindingDependencies ([(0,44),(1,38)] : List (Nat × Nat))).length = 82 := by decide

#print axioms prepareStamped_regroup
#print axioms bindingDependencies_count_le

#print axioms prepareStamped_grouped
#print axioms groupedDependencies_length_le

#print axioms prepareStamped_transport
#print axioms prepareStamped_stale_producer

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

/-- Two services share a callback handle, represented abstractly by its stable id. -/
def batchBase (key : Nat) : Option (Nat × Int) :=
  if key = 1 ∨ key = 9 then some (41, 10) else none

/-- Three rounds update, delete, then reinsert one service with the same callback. -/
def serviceBatches : List (List (Change Nat (Nat × Int))) :=
  [[⟨1, some (41, 10), some (41, 20)⟩],
   [⟨1, some (41, 20), none⟩, ⟨2, none, some (41, 5)⟩],
   [⟨1, none, some (41, 30)⟩, ⟨2, some (41, 5), none⟩]]

example : (batchChanges serviceBatches).length = 5 := by decide

/-- The temporary service disappears while the shared unrelated handle survives. -/
example : (applyChanges (batchChanges serviceBatches) batchBase).map
    (fun view => (view 1, view 2, view 9)) =
      .ok (some (41, 30), none, some (41, 10)) := by rfl

/-- General sequential equivalence applies to all keys and repeated edits. -/
example : applyChanges (batchChanges serviceBatches) batchBase =
    applyBatches serviceBatches batchBase := batchChanges_correct _ _

/-- A late conflicting request keeps the exact first refusal key. -/
example : applyBatches
    (serviceBatches ++ [[⟨1, some (41, 10), some (41, 40)⟩]]) batchBase = .error 1 := by rfl

/-- An aggregate consumer cannot receive a state from a failed complete batch. -/
example : applyFold (fun _ value => value.2)
    (batchChanges (serviceBatches ++ [[⟨1, some (41, 10), some (41, 40)⟩]])) batchBase 20 =
      .error 1 := applyFold_batch_error _ _ _ _ _ (by rfl)

/-- A fresh retry expects the current value and updates both ledger and aggregate. -/
example : (applyFold (fun _ value => value.2)
    (batchChanges (serviceBatches ++ [[⟨1, some (41, 30), some (41, 40)⟩]])) batchBase 20).map
      (fun result => (result.1 1, result.2)) = .ok (some (41, 40), 50) := by rfl

/-- Undo retracts every intermediate contribution, including the temporary service. -/
example : foldChanges (fun _ value => value.2) (inverseChanges (batchChanges serviceBatches))
    (foldChanges (fun _ value => value.2) (batchChanges serviceBatches) 20) = 20 :=
  foldChanges_inverse _ _ _

/-- Cancelling writes cannot be squashed: the stale base must still refuse. -/
example : applyChanges ([⟨1, some 10, some 11⟩, ⟨1, some 11, some 10⟩] : List (Change Nat Int))
    (fun _ => some 99) = .error 1 := by rfl

/-- Empty operation lists alone have no such conflict observation. -/
example : (applyChanges ([] : List (Change Nat Int)) (fun _ => some 99)).map
    (fun view => view 1) = .ok (some 99) := by rfl

/-- Pair-shaped keys are an explicit representation isomorphism. -/
def batchKeys : Prototype.DictionaryBridge Nat (Nat × Unit) :=
  ⟨fun key => (key, ()), Prod.fst, fun _ => rfl, fun pair => by cases pair; rfl⟩

/-- Rearranging a capacity and callback handle leaves the handle untouched. -/
def batchValues : Prototype.DictionaryBridge (Nat × Int) (Int × Nat) :=
  ⟨Prod.swap, Prod.swap, fun _ => rfl, fun _ => rfl⟩

/-- Whole-batch transport preserves intermediate checks and the mapped error key. -/
example : applyChanges (transportChanges batchKeys batchValues (batchChanges serviceBatches))
      (transportView batchKeys batchValues batchBase) =
    ((applyChanges (batchChanges serviceBatches) batchBase).mapError batchKeys.toFields).map
      (transportView batchKeys batchValues) := transport_applyChanges _ _ _ _

/-- An origin with no writes remains a dependency after composition. -/
example : stampMatches ([[] , [7], [8]] : List (List Nat)).flatten
    (fun _ => some 1) (fun key => if key = 7 then some 2 else some 1) = false := by decide


/-- Key negation is an explicit involution, rather than an inferred ordering rule. -/
def mirroredKeys : Prototype.DictionaryBridge Int Int :=
  ⟨Neg.neg, Neg.neg, fun key => Int.neg_neg key, fun key => Int.neg_neg key⟩

/-- Reuse the same persistent write primitive and retain unrelated service metadata. -/
def mirroredSource : TableCarrier Int (Nat × Int) ((Int → Option (Nat × Int)) × String) where
  read := Prod.fst
  write := fun source key value => (replace source.1 key value, source.2)
  read_write := fun _ _ _ => rfl

/-- The raw target rearranges the host carrier without defining a new table backend. -/
def mirroredRepresentation : Prototype.DictionaryBridge
    ((Int → Option (Nat × Int)) × String) (String × (Int → Option (Nat × Int))) :=
  ⟨Prod.swap, Prod.swap, fun _ => rfl, fun _ => rfl⟩

/-- Derive every optional-write operation from the original carrier and three bridges. -/
def mirroredTable := mirroredSource.conjugate mirroredKeys batchValues mirroredRepresentation

/-- Shared callback handles stay abstract; the independent host label is retained. -/
def mirroredBase : (Int → Option (Nat × Int)) × String :=
  (fun key => if key = 1 then some (41, 10) else if key = 9 then some (41, 90) else none, "capacity")

/-- Consecutive revisions include deletion/reinsertion and a temporary service. -/
def mirroredEdits : List (Change Int (Nat × Int)) :=
  [⟨1, some (41, 10), some (41, 20)⟩,
   ⟨1, some (41, 20), none⟩, ⟨2, none, some (41, 5)⟩,
   ⟨1, none, some (41, 30)⟩, ⟨2, some (41, 5), none⟩]

/-- The generated read changes key/value representation, not callback identity. -/
example : mirroredTable.read (mirroredRepresentation.toFields mirroredBase) (-1) = some (10, 41) := by rfl

/-- The generated installer preserves the shared service and unrelated host label. -/
example : (mirroredTable.apply (transportChanges mirroredKeys batchValues mirroredEdits)
    (mirroredRepresentation.toFields mirroredBase)).map
      (fun target => (target.1, mirroredTable.read target (-1), mirroredTable.read target (-2),
        mirroredTable.read target (-9))) =
      .ok ("capacity", some (30, 41), none, some (90, 41)) := by rfl

/-- The general theorem covers the complete carrier, every key and every first error. -/
example : mirroredTable.apply (transportChanges mirroredKeys batchValues mirroredEdits)
      (mirroredRepresentation.toFields mirroredBase) =
    ((mirroredSource.apply mirroredEdits mirroredBase).mapError mirroredKeys.toFields).map
      mirroredRepresentation.toFields := mirroredSource.conjugate_apply _ _ _ _ _

/-- A later competing request exposes the negated first conflict key. -/
example : mirroredTable.apply (transportChanges mirroredKeys batchValues
    (mirroredEdits ++ [⟨1, some (41, 10), some (41, 40)⟩]))
    (mirroredRepresentation.toFields mirroredBase) = .error (-1) := by rfl

/-- Standard folds preserve source traversal order even when keys are negated. -/
example : transportBindings mirroredKeys batchValues [(1, (41, 10)), (9, (41, 90))] =
    [(-1, (10, 41)), (-9, (90, 41))] := by decide

/-- Inverting the derivation recovers the original complete read/write algorithms. -/
example : (mirroredTable.conjugate mirroredKeys.inverse batchValues.inverse mirroredRepresentation.inverse).read =
      mirroredSource.read ∧
    (mirroredTable.conjugate mirroredKeys.inverse batchValues.inverse mirroredRepresentation.inverse).write =
      mirroredSource.write := mirroredSource.conjugate_inverse _ _ _

end LeanPoo.Examples.TableRevision

-- Identical complete stage work, with three fewer nested entry invocations.
example : LeanPoo.Functional.OrderedDictionary.checkedEntryCost [90, 20, 15, 75] 1 3 = 203 := by decide
example : LeanPoo.Functional.OrderedDictionary.checkedEntryCost [90, 20, 15, 75] 4 3 = 212 := by decide
#print axioms LeanPoo.Functional.OrderedDictionary.checkedEntryCost_shared

-- The first refusal survives flattening; the workload result is not selected.
example : LeanPoo.Functional.OrderedDictionary.runEntryChecks
    [(fun _ => Except.ok ()), (fun _ => Except.error "module"),
      (fun _ => Except.error "workload")] = (Except.error "module" : Except String Unit) := rfl
#print axioms LeanPoo.Functional.OrderedDictionary.runEntryChecks_append

-- Audit the new batch laws for unintended proof assumptions.
#print axioms LeanPoo.Functional.OrderedDictionary.batchChanges_correct
#print axioms LeanPoo.Functional.OrderedDictionary.batchChanges_append
#print axioms LeanPoo.Functional.OrderedDictionary.batchChanges_associative
#print axioms LeanPoo.Functional.OrderedDictionary.batchChanges_inverse
#print axioms LeanPoo.Functional.OrderedDictionary.applyBatches_inverse
#print axioms LeanPoo.Functional.OrderedDictionary.transport_batchChanges
#print axioms LeanPoo.Functional.OrderedDictionary.foldChanges_append
#print axioms LeanPoo.Functional.OrderedDictionary.applyFold_batch_error
#print axioms LeanPoo.Functional.OrderedDictionary.batchChanges_length
#print axioms LeanPoo.Functional.OrderedDictionary.batch_foldWork_bound
#print axioms LeanPoo.Functional.OrderedDictionary.pruneDeletedOwners_live
#print axioms LeanPoo.Functional.OrderedDictionary.batch_stampMatches

-- Audit representation derivation laws independently of the Scheme runtime.
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_read
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_write
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_apply
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_batch
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_undo
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_inverse
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_trans_read
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_trans_write
#print axioms LeanPoo.Functional.OrderedDictionary.transportBindings_length
#print axioms LeanPoo.Functional.OrderedDictionary.transportBindings_foldl
#print axioms LeanPoo.Functional.OrderedDictionary.transportBindings_foldr
#print axioms LeanPoo.Functional.OrderedDictionary.transportBindings_inverse
#print axioms LeanPoo.Functional.OrderedDictionary.wrapper_sources_current

#print axioms LeanPoo.Functional.OrderedDictionary.wrapper_sources_nested
#print axioms LeanPoo.Functional.OrderedDictionary.conjugate_codec_roundtrip

#print axioms LeanPoo.Functional.OrderedDictionary.pair_codec_roundtrip

-- The structural codec model evaluates the left child before the right thunk.
example {A B E : Type} (cause : E) (right : Unit → Except E B) :
    (Except.error cause : Except E A).bind
      (fun left => (right ()).map (fun value => (left, value))) = .error cause := rfl
