import LeanPoo.Functional.TableOrder

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

/-- Every generated style executes the derived ledger's repeated edits with the
same host label, shared callback handles and temporary-service removal. -/
example (style : TableStyle) :
    (styleStep style (some (mirroredRepresentation.toFields mirroredBase))
      (mirroredTable.apply (transportChanges mirroredKeys batchValues mirroredEdits))).2.map
      (fun target => (target.1, mirroredTable.read target (-1), mirroredTable.read target (-2),
        mirroredTable.read target (-9))) =
      .ok ("capacity", some (30, 41), none, some (90, 41)) := by
  cases style <;> rfl

/-- A late conflicting edit retires no owner and retains the exact old carrier. -/
example (style : TableStyle) :
    styleStep style (some (mirroredRepresentation.toFields mirroredBase))
      (mirroredTable.apply (transportChanges mirroredKeys batchValues
        (mirroredEdits ++ [⟨1, some (41, 10), some (41, 40)⟩]))) =
      (some (mirroredRepresentation.toFields mirroredBase), .error (.callback (-1))) := rfl

/-- The explicit comparison matches the three-way protocol used by Gerbil. -/
def priorityCompare (a b : Int) : Int := if a < b then -1 else if a = b then 0 else 1

/-- External negative identifiers keep ascending internal priority, not host order. -/
example : checkedTableRange (transportComparer mirroredKeys priorityCompare)
    (some ⟨-10, false⟩) (some ⟨-40, true⟩)
    ([(-10, 1), (-20, 2), (-30, 3), (-40, 1)] : List (Int × Nat)) =
    .ok [(-20, 2), (-30, 3), (-40, 1)] := by rfl

/-- Reversed priority endpoints are a refusal rather than an empty successful query. -/
example : checkedTableRange (transportComparer mirroredKeys priorityCompare)
    (some ⟨-40, true⟩) (some ⟨-10, true⟩) ([] : List (Int × Nat)) = .error () := by rfl

/-- Opaque service callbacks survive the transported interval unchanged. -/
example (callback : Int → Int) :
    tableRangeRows (transportComparer mirroredKeys priorityCompare)
      (some ⟨-20, true⟩) none [(-10, callback), (-20, callback), (-30, callback)] =
      [(-20, callback), (-30, callback)] := by rfl

/-- The positioned loop reads the first excluded boundary but not its suffix. -/
example : tableRangePrefix (fun key : Nat => decide (key ≤ 1803))
    [(1800, 42), (1801, 42), (1802, 42), (1803, 42), (1804, 42), (9000, 42)] =
    ([(1800, 42), (1801, 42), (1802, 42), (1803, 42)], 5) := rfl

/-- An already exhausted cursor still performs one EOF observation. -/
example : tableRangePrefix (fun _ : Nat => true) ([] : List (Nat × Nat)) = ([], 1) := rfl

#print axioms tableRangeWindow_correct
#print axioms tableRangePrefix_pulls
#print axioms tableRangePrefix_work

#print axioms transportComparer_laws
#print axioms tableRangeRows_transport
#print axioms tableRangeRows_ordered

/-- A bounded service builder retains an opaque checked callback on every update. -/
def boundedServiceUpdate (limit : Nat) (state : Nat × (Int → Int)) (amount : Nat) :
    Except String (Nat × (Int → Int)) :=
  if state.1 + amount ≤ limit then .ok (state.1 + amount, state.2)
  else .error "capacity exceeded"

/-- The finite builder's successful updates preserve the admitted carrier bound. -/
theorem boundedServiceUpdate_preserves (limit : Nat) (state : Nat × (Int → Int))
    (amount : Nat) (next : Nat × (Int → Int))
    (_admitted : decide (state.1 ≤ limit) = true)
    (success : boundedServiceUpdate limit state amount = .ok next) :
    decide (next.1 ≤ limit) = true := by
  simp only [boundedServiceUpdate] at success
  split at success
  · simp only [Except.ok.injEq] at success
    subst next
    simpa
  · simp at success

/-- One admission and per-prefix admission have identical callback/error results. -/
example (limit : Nat) (callback : Int → Int) (edits : List Nat) :
    checkedShapeUpdates (fun state => decide (state.1 ≤ limit)) "shape refused"
      (boundedServiceUpdate limit) (0, callback) edits =
      edits.foldlM (boundedServiceUpdate limit) (0, callback) :=
  checkedShapeUpdates_reuse _ _ _ (boundedServiceUpdate_preserves limit) _ (by simp) edits

/-- Refusal preserves the precise update error; a fresh bounded retry can succeed. -/
example (callback : Int → Int) :
    checkedShapeUpdates (fun state => decide (state.1 ≤ 5)) "shape refused"
      (boundedServiceUpdate 5) (0, callback) [1, 2, 9] = .error "capacity exceeded" := rfl

/-- The retry's carrier contains the exact original callback, without rewrapping. -/
example (callback : Int → Int) :
    checkedShapeUpdates (fun state => decide (state.1 ≤ 5)) "shape refused"
      (boundedServiceUpdate 5) (0, callback) [1, 2] = .ok (3, callback) := rfl

#print axioms checkedShapeUpdates_admit_equiv
#print axioms checkedShapeUpdates_reuse
#print axioms checkedShapeUpdates_valid
#print axioms repeatedShapeWork_square

/-- The traversal certificate separates a shared false-valued row from a new
smaller key and a removed larger key; insertions must still be emitted last. -/
def booleanRevisionTraversal : DeltaTraversal Nat Bool :=
  .fork (.changed ⟨0, none, some false⟩)
    (.fork (.shared [(8, false)]) (.changed ⟨20, some true, none⟩))

/-- An insertion at zero cannot precede the deletion at twenty. -/
example : (prunedDelta booleanRevisionTraversal).map Change.key = [20, 0] := rfl

/-- A stale old binding refuses at the same first key, without partial publication. -/
example : applyChanges (prunedDelta booleanRevisionTraversal) (fun _ => none) = .error 20 := rfl

/-- Missing and stored false remain distinct after successful installation. -/
example : (applyChanges (prunedDelta booleanRevisionTraversal)
    (fun key => if key = 8 then some false else if key = 20 then some true else none)).map
      (fun view => (view 0, view 8, view 20)) = .ok (some false, some false, none) := rfl

/-- Undo restores the original observations without recomputing the shared rows. -/
example : (applyChanges (inverseChanges (prunedDelta booleanRevisionTraversal))
    (fun key => if key = 0 ∨ key = 8 then some false else none)).map
      (fun view => (view 0, view 8, view 20)) = .ok (none, some false, some true) := rfl

/-- A shared region of arbitrary size contributes one visit per pair pass. -/
example (rows : List (Nat × Bool)) (edit : Change Nat Bool) :
    prunedDeltaWork (.fork (.shared rows) (.changed edit)) = 3 := rfl

#print axioms prunedDelta_correct
#print axioms prunedDelta_install
#print axioms prunedDelta_inverse
#print axioms prunedDelta_work

/-- Services may belong to several teams, including repeated or empty memberships. -/
def taggedBefore (key : Nat) : Option (List Nat × Nat) :=
  if key = 1 then some ([10, 20, 10], 42)
  else if key = 2 then some ([20, 30], 42)
  else if key = 9 then some ([], 42) else none

/-- Atomic migration changes both shared memberships and retains the payload token. -/
def taggedAfter (key : Nat) : Option (List Nat × Nat) :=
  if key = 1 then some ([30, 40], 42)
  else if key = 2 then some ([10, 40, 40], 42)
  else if key = 9 then some ([], 42) else none

/-- Two touched columns rebuild every team, including removal and shared insertion. -/
theorem taggedMigration :
    reviseIndexKeys [1, 2] (fun _ row => row.1) taggedAfter
      (indexKeysView (fun _ row => row.1) taggedBefore) =
    indexKeysView (fun _ row => row.1) taggedAfter := by
  apply reviseIndexKeys_correct
  intro key outside
  simp only [List.mem_cons, List.mem_singleton, not_or] at outside
  simp [taggedBefore, taggedAfter, outside.1, outside.2]

example : indexKeysView (fun _ row => row.1) taggedAfter 20 1 = none := by decide
example : indexKeysView (fun _ row => row.1) taggedAfter 40 2 = some ([10, 40, 40], 42) := by decide
example : indexKeysView (fun _ row => row.1) taggedBefore 20 9 = none := by decide

/-- Existing aliases are disjoint across owners; one owner may have several aliases. -/
def aliasOwners (key : Nat) : Option Nat :=
  if key = 101 ∨ key = 111 then some 1
  else if key = 102 ∨ key = 112 then some 2 else none

/-- A fresh first alias cannot conceal the exact later collision. -/
example : (claimIndexKeys aliasOwners [200, 111, 101] 2).map (fun _ => ()) =
    .error (111, (1, 2)) := by rfl

/-- Repeated claims by the same owner are accepted without changing observations. -/
example : (claimIndexKeys aliasOwners [200, 200] 2).map (fun owners => owners 200) =
    .ok (some 2) := by rfl

/-- A live outer view cannot authorize a cursor whose inner revision changed. -/
example : (if ([4, 9] : List Nat) = [4, 9] then
    checkedTablePull [2, 7] [2, 8] [(120, 42), (121, 42)] else (.error (), 0)) =
    ((.error (), 0) : Except Unit (Option (Nat × Nat) × List (Nat × Nat)) × Nat) := by rfl

/-- A resumed cursor keeps the exact opaque service callback and remaining tail. -/
example (callback : Int → Int) : checkedTablePull [4, 9] [4, 9]
    [(120, callback), (121, callback)] =
    (.ok (some (120, callback), [(121, callback)]), 1) := by rfl

/-- A stale exhausted cursor refuses rather than returning another successful EOF. -/
example : checkedTablePull (K := Nat) (V := Nat) [4, 9] [4, 10] [] = (.error (), 0) := by rfl

/-- Point capture preserves a shared service token while a later unrelated rebase survives. -/
example : (applyChanges (pointChanges (fun k : Nat => if k = 1 then some 42 else none) 1 (some 43))
    (fun k => if k = 1 then some 42 else if k = 9 then some 90 else none)).map
    (fun view => (view 1, view 9)) = .ok (some 43, some 90) := by rfl

/-- Stored false and absence remain distinct in a single optional removal request. -/
example : pointChanges (fun _ : Nat => some false) 1 none = [⟨1, some false, none⟩] := by rfl

/-- An unchanged request is empty, matching .diff rather than claiming a read lock. -/
example : pointChanges (fun _ : Nat => some false) 1 (some false) = [] := by rfl

/-- Lower mean wall cost can coexist with an adverse tail; do not admit an
entry-level latency claim from the aggregate saving alone. Units are arbitrary. -/
example : ([-1000, -1000, 500] : List Int).sum < 0 ∧
    measuredTail [-1000, -1000, 500] = 500 := by decide

/-- A preparation saving is insufficient when GC/residual growth exceeds it,
even with identical first-call, prefix and complete batch costs. -/
example : measuredEntry 5 10 10 100 5 30 2 > measuredEntry 10 10 10 100 5 20 0 := by decide

/-- Declaration, backend and child metadata remain correlated over any accepted
finite callback edit trace outside the complete nested preparation scope. -/
example (edits : List (Change Nat Nat)) (before after : Nat → Option Nat)
    (guarded : ∀ edit ∈ edits, edit.key ∉
      extendProtection [2] (extendProtection [1] [0] false) false)
    (accepted : applyChanges edits before = .ok after) :
    after 0 = before 0 ∧ after 1 = before 1 ∧ after 2 = before 2 := by
  have frame := indexPreparation_frame [0] [1] [2] edits before after guarded accepted
  exact ⟨frame 0 (by simp), frame 1 (by simp), frame 2 (by simp)⟩

/-- Sampling a revision only after a permitted late rewrite would certify the
wrong recipe; protecting participants before reading recipes is essential. -/
example : (applyChanges [⟨0, some 7, some 107⟩] (fun _ : Nat => some (7 : Nat))).map
      (fun state => state 0) = .ok (some 107) := rfl

/-- The reporter retains the first measured callback handle if the paired
second action refuses; deferred observation never invents a successful second row. -/
example (callback : Int → Int) :
    measurePair (fun candidate => if candidate then Except.error "sample refused"
      else Except.ok callback) [false, true] = ([(false, callback)], .error "sample refused") := rfl

/-- Reversed matched order retains both exact observations, rather than sorting
rows or dropping an adverse result before reporting the pair. -/
example : measurePair (fun candidate => Except.ok (if candidate then (-7 : Int) else 9) :
    Bool → Except String Int) [true, false] = ([(true, -7), (false, 9)], .ok ()) := rfl

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

-- All styles expose the same complete backend result, including first refusal.
example (state : Option Int) (update : Int → Except String Int) :
    (LeanPoo.Functional.OrderedDictionary.styleStep .pure state update).2 =
      (LeanPoo.Functional.OrderedDictionary.styleStep .linear state update).2 :=
  LeanPoo.Functional.OrderedDictionary.styleStep_result _ _ _ _

-- A successful mutable installation preserves its snapshot as an independent pure value.
example : LeanPoo.Functional.OrderedDictionary.styleStep .mutable (some (10 : Int))
    (fun value => (Except.ok (value + 5) : Except String Int)) = (some 15, .ok 15) := rfl

-- Failure never consumes the old capability; a later explicit retry can succeed.
example : LeanPoo.Functional.OrderedDictionary.styleStep .linear (some (10 : Int))
    (fun _ => (Except.error "late conflict" : Except String Int)) =
      (some 10, .error (.callback "late conflict")) := rfl

-- Same-style conversion also retires an owned reference; snapshot reads are separate.
example : LeanPoo.Functional.OrderedDictionary.styleConvert (E := String) .linear .linear
    (some (42 : Int)) = (none, .ok (.linear, 42)) := rfl

#print axioms LeanPoo.Functional.OrderedDictionary.styleStep_linear_existing
#print axioms LeanPoo.Functional.OrderedDictionary.styleStep_table_conflict
#print axioms LeanPoo.Functional.OrderedDictionary.installStyle_aba


namespace LeanPoo.Examples.TableRevision
open LeanPoo.Functional.OrderedDictionary

/-- Two unique identifier declarations and a grouped declaration have typed keys. -/
inductive ServiceIndex where
  | badge | endpoint | team
  deriving DecidableEq, Repr

/-- Badge and endpoint keys are numeric; team keys also carry a grouping flag. -/
abbrev serviceIndexKey : ServiceIndex → Type
  | .badge | .endpoint => Nat
  | .team => Nat × Bool

instance (name : ServiceIndex) : DecidableEq (serviceIndexKey name) := by
  cases name <;> exact inferInstance

/-- Final values include a shared opaque callback handle in the fourth field. -/
abbrev IndexedService := Nat × Nat × Nat × Nat

/-- The existing persistent optional-write carrier supplies all primary changes. -/
def indexedPrimary : TableCarrier Nat IndexedService (Nat → Option IndexedService) where
  read := id
  write := replace
  read_write := fun _ _ _ => rfl

/-- Each declaration observes one already admitted primary row. -/
def serviceIndexProject : (name : ServiceIndex) → Nat → IndexedService → serviceIndexKey name
  | .badge => fun _ row => row.1
  | .endpoint => fun _ row => row.2.1
  | .team => fun _ row => (row.2.2.1, true)

/-- Grouped declarations allow several primary owners in the same bucket. -/
def serviceIndexUnique : ServiceIndex → Bool
  | .badge | .endpoint => true
  | .team => false

/-- Initial services share a team and callback, alongside an untouched service. -/
def indexedBefore (key : Nat) : Option IndexedService :=
  if key = 1 then some (101, 1001, 10, 42)
  else if key = 2 then some (102, 1002, 10, 42)
  else if key = 9 then some (109, 1009, 90, 42) else none

/-- The finite oracle enumerates the final fixture's complete live support. -/
def enumerateIndexed (primary : Nat → Option IndexedService) : List (Nat × IndexedService) :=
  [1, 2, 9].filterMap fun key => (primary key).map fun row => (key, row)

/-- Transient collisions and repeated keys are retained in the primary batch. -/
def indexedChanges : List (Change Nat IndexedService) :=
  [⟨1, some (101, 1001, 10, 42), some (102, 1002, 20, 42)⟩,
   ⟨2, some (102, 1002, 10, 42), some (101, 1001, 20, 42)⟩,
   ⟨1, some (102, 1002, 20, 42), none⟩,
   ⟨3, none, some (103, 1003, 30, 42)⟩,
   ⟨1, none, some (102, 1002, 20, 42)⟩,
   ⟨3, some (103, 1003, 30, 42), none⟩]

/-- The atomic result synchronizes every typed index while retaining shared payloads. -/
example : (applyIndexed indexedPrimary [.badge, .endpoint, .team] serviceIndexUnique
    serviceIndexProject enumerateIndexed indexedChanges
      (indexedBefore, correlatedViews serviceIndexProject indexedBefore)).map
        (fun state => (state.1 1, state.2 .badge 102 1, state.2 .team (20, true) 2, state.1 9)) =
    .ok (some (102, 1002, 20, 42), some (102, 1002, 20, 42),
      some (101, 1001, 20, 42), some (109, 1009, 90, 42)) := by rfl

/-- A fresh badge cannot hide a collision in the later unique endpoint declaration. -/
example : applyIndexed indexedPrimary [.badge, .endpoint, .team] serviceIndexUnique
    serviceIndexProject enumerateIndexed [⟨1, some (101, 1001, 10, 42), some (103, 1002, 20, 42)⟩]
      (indexedBefore, correlatedViews serviceIndexProject indexedBefore) = .error (.inr .endpoint) := by rfl

/-- Primary conflict has precedence over a later possible uniqueness violation. -/
example : applyIndexed indexedPrimary [.badge, .endpoint, .team] serviceIndexUnique
    serviceIndexProject enumerateIndexed [⟨1, none, some (103, 1002, 20, 42)⟩]
      (indexedBefore, correlatedViews serviceIndexProject indexedBefore) = .error (.inl 1) := by rfl

end LeanPoo.Examples.TableRevision

#print axioms LeanPoo.Functional.OrderedDictionary.applyIndexed_correlated
#print axioms LeanPoo.Functional.OrderedDictionary.checkIndexRows_ownership
#print axioms LeanPoo.Functional.OrderedDictionary.indexed_cache_inverse


namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- Quote a read plus an equality comparison on every attempted edit; only
successful comparisons incur the persistent backend write. Units are abstract. -/
def revisionQuote (_ : Nat → Option Bool) (_ : Change Nat Bool) (ok : Bool) : Nat :=
  3 + if ok then 5 else 0

/-- A late conflict pays one successful write and the next comparison, with no
suffix installation. The complete error semantics remain the existing ones. -/
example : viewCarrier.applyCost revisionQuote
    [⟨1, some false, some true⟩, ⟨2, some false, none⟩, ⟨9, some true, none⟩] original = 11 := by
  rfl

/-- An early conflict does not pay the cold setup again, nor a successful write;
setup and output observation remain separate in the full-workflow sum. -/
example : tableWorkflowCost 8
    (viewCarrier.applyCost revisionQuote [⟨2, some false, none⟩] original) 20 0 = 31 := by
  rfl

/-- Reducing an install by ten units is insufficient if conversion/preparation
adds eleven. This negative control prevents an allocation-only speedup claim. -/
example : ¬ tableWorkflowCost (8 + 11) (30 - 10) 20 8 ≤
    tableWorkflowCost 8 30 20 8 := by decide

end LeanPoo.Examples.TableRevision

#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.applyCost_conflict
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.applyCost_add
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_cost
#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.conjugate_cost_overhead
#print axioms LeanPoo.Functional.OrderedDictionary.tableWorkflowCost_breakEven
#print axioms LeanPoo.Functional.OrderedDictionary.carrier_check_share


namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- Four repeated conversion visits repay the quoted full metadata preparation
premium; conversion and equality remain in the common 90-unit work quote. -/
example : typeContextCost (20 + 128) 4 2 90 ≤ typeContextCost 20 4 (2 + 28) 90 := by
  decide

/-- A one-visit cold path cannot amortize that same metadata preparation premium. -/
example : ¬ typeContextCost (20 + 128) 1 2 90 ≤ typeContextCost 20 1 (2 + 28) 90 := by
  decide

/-- GC/preparation may consume the entire nominal lookup saving. Lower access
counts alone do not justify admitting this adverse complete-workflow quote. -/
example : ¬ typeContextCost (20 + 225) 4 2 90 ≤ typeContextCost 20 4 (2 + 28) 90 := by
  decide

end LeanPoo.Examples.TableRevision

#print axioms LeanPoo.Functional.OrderedDictionary.TableCarrier.applyCost_scale
#print axioms LeanPoo.Functional.OrderedDictionary.typeContextCost_breakEven
#print axioms LeanPoo.Functional.OrderedDictionary.transportBindings_captured
#print axioms LeanPoo.Functional.OrderedDictionary.typeContext_stale

/-- A cached Type cannot bypass an observed access denial. -/
example : LeanPoo.Functional.OrderedDictionary.readTypeContext true
    (fun _ => Except.error "denied") (7 : Nat) = .error "denied" := rfl

#print axioms LeanPoo.Functional.OrderedDictionary.readTypeContext_denied
#print axioms LeanPoo.Functional.OrderedDictionary.readTypeContext_current

namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- A truncated revision vector must refuse, even if its shared prefix agrees. -/
example : revisionsCurrent [0, 1] [7] (fun _ => 7) = false := by decide
example : revisionsCurrent [0] [7, 7] (fun _ => 7) = false := by decide
example : revisionsCurrent [0, 1, 2] [7, 7, 8] (fun _ => 7) = false := by decide
example : revisionsCurrent [0, 1, 2] [7, 7, 7] (fun _ => 7) = true := by decide

/-- Rounded tenth-microsecond control from the adverse retry batch: lower
non-GC CPU and lower total CPU still coexist with higher observed wall time. -/
example : 21849 < 23209 ∧ 21849 + 2292 < 23209 + 1598 ∧
    measuredWall 23209 1598 189 < measuredWall 21849 2292 22429 := by decide

end LeanPoo.Examples.TableRevision

#print axioms LeanPoo.Functional.OrderedDictionary.revisionsCurrent_eq
#print axioms LeanPoo.Functional.OrderedDictionary.measuredWall_bound

/-- Generic structural equality refuses a malformed revision without numeric
coercion; the Scheme boundary separately refuses improper version lists. -/
example : LeanPoo.Functional.OrderedDictionary.revisionsCurrent
    [0, 1] [some 7, none] (fun _ => some 7) = false := by decide

/-- The prepared receiver is covered even when it was absent from origin metadata. -/
example : LeanPoo.Functional.OrderedDictionary.receiverScope (some "receiver")
    ["source", "key", "value"] = ["receiver", "source", "key", "value"] := rfl
example : LeanPoo.Functional.OrderedDictionary.receiverScope (none : Option Nat) [1, 2] = [1, 2] := rfl
#print axioms LeanPoo.Functional.OrderedDictionary.receiverScope_closed

namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- Reorder a bounded service's capacity and opaque callback without cloning it. -/
def boundedServiceCarrier : Prototype.DictionaryBridge
    (Nat × (Int → Int)) ((Int → Int) × Nat) :=
  ⟨Prod.swap, Prod.swap, fun _ => rfl, fun _ => rfl⟩

/-- The existing persistent-shape theorem transfers to represented service
updates, retaining ordered failure and the exact callback through retries. -/
example (limit : Nat) (target : (Int → Int) × Nat) (edits : List Nat) :
    checkedShapeUpdates (fun t => decide (t.2 ≤ limit)) "shape refused"
        (fun t edit => (boundedServiceUpdate limit (t.2, t.1) edit).map Prod.swap) target edits =
      admittedShapeUpdates (fun t => decide (t.2 ≤ limit)) "shape refused"
        (fun t edit => (boundedServiceUpdate limit (t.2, t.1) edit).map Prod.swap) target edits :=
  representedShapeUpdates_reuse boundedServiceCarrier _ _ _ (boundedServiceUpdate_preserves limit) _ _

/-- An over-capacity first attempt refuses; a fresh smaller retry retains the
same callback while admission can reuse the declared update-closure law. -/
example (callback : Int → Int) :
    admittedShapeUpdates (fun t => decide (t.2 ≤ 5)) "shape refused"
      (fun t edit => (boundedServiceUpdate 5 (t.2, t.1) edit).map Prod.swap)
      (callback, 0) [1, 2, 9] = .error "capacity exceeded" := rfl
example (callback : Int → Int) :
    admittedShapeUpdates (fun t => decide (t.2 ≤ 5)) "shape refused"
      (fun t edit => (boundedServiceUpdate 5 (t.2, t.1) edit).map Prod.swap)
      (callback, 0) [1, 2] = .ok (callback, 3) := rfl

end LeanPoo.Examples.TableRevision
#print axioms LeanPoo.Functional.OrderedDictionary.representedShapeUpdate_preserves
#print axioms LeanPoo.Functional.OrderedDictionary.representedShapeUpdates_reuse

/-- A declared shape law cannot replace read authority in the observed route. -/
example : LeanPoo.Functional.OrderedDictionary.readTypeContext true
    (fun _ => Except.error "validator denied") (true : Bool) = .error "validator denied" := rfl

#print axioms LeanPoo.Functional.OrderedDictionary.measuredEntry_prepare_bound
#print axioms LeanPoo.Functional.OrderedDictionary.measuredTail_bound

#print axioms LeanPoo.Functional.OrderedDictionary.indexPreparation_frame
#print axioms LeanPoo.Functional.OrderedDictionary.indexPreparation_current

#print axioms LeanPoo.Functional.OrderedDictionary.measurePair_status
#print axioms LeanPoo.Functional.OrderedDictionary.measurePair_second_error
#print axioms LeanPoo.Functional.OrderedDictionary.measurePair_complete

namespace LeanPoo.Examples.TableRevision
open Functional.OrderedDictionary

/-- Same endpoint identities admit both ordinary transport and derived folds. -/
def serviceTranslationMetadata (id : Nat) : Option (Nat × Nat) :=
  match id with
  | 0 => some (7, 8)
  | 1 => some (9, 10)
  | 2 => some (7, 9)
  | 3 => some (8, 10)
  | _ => none

example : translationTypesAgree serviceTranslationMetadata 0 1 2 3 = true := rfl

/-- A later getter's rewrite of the earlier converter invalidates the declaration,
even though capturing revision stamps after that rewrite could look current. -/
example : translationTypesAgree
    (fun id => if id = 2 then some (11, 9) else serviceTranslationMetadata id)
    0 1 2 3 = false := rfl

/-- Supported edits outside the complete scope preserve exact endpoint admission. -/
example (edits : List (Change Nat (Nat × Nat))) (after : Nat → Option (Nat × Nat))
    (guarded : ∀ edit ∈ edits, edit.key ∉
      extendProtection [6] (extendProtection [4, 5] [0, 1, 2, 3] false) false)
    (accepted : applyChanges edits serviceTranslationMetadata = .ok after) :
    translationTypesAgree after 0 1 2 3 = true :=
  (translationPreparation_compatible 0 1 2 3 [4, 5] [6] edits
    serviceTranslationMetadata after guarded accepted).trans rfl

/-- Reduced collector work alone cannot justify a worse complete-entry tail. -/
example : ¬ measuredEntry 20 5 5 10 0 1 100 ≤ measuredEntry 20 5 5 10 0 9 0 := by decide

end LeanPoo.Examples.TableRevision
#print axioms LeanPoo.Functional.OrderedDictionary.translationPreparation_compatible
#print axioms LeanPoo.Functional.OrderedDictionary.measuredEntry_gc_bound
