-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.SourcePreparation
import LeanPoo.Functional.GraphRevision
import LeanPoo.Functional.ComponentPublication

/-! Exact raw-storage registration for composite prototype views.
These are source/certificate contracts, not another evaluator or cache.
List operations specify existing ordinal-index updates; they are not a proposal
to replace native indexed put with a linear scan. -/
namespace LeanPoo.Object.SourceViews

open SourcePreparation

abbrev Rows (Key : Type) := List (Key × Handle)
abbrev Counts := Nat → Nat

def owners {Key : Type} (rows : Rows Key) : List Nat :=
  rows.map fun row => row.2.source

def occurrences {Key : Type} (rows : Rows Key) (owner : Nat) : Nat :=
  (owners rows).count owner

def increment (counts : Counts) (owner : Nat) : Counts :=
  fun query => if query = owner then counts query + 1 else counts query

def decrement (counts : Counts) (owner : Nat) : Counts :=
  fun query => if query = owner then counts query - 1 else counts query

/-- The actual initial admission fold counts contributions once. It does not
deduplicate by key: later contributions to the same slot still own raw storage. -/
def admitCounts {Key : Type} (rows : Rows Key) : Counts :=
  rows.foldl (fun counts row => increment counts row.2.source) (fun _ => 0)

private theorem fold_counts {Key : Type} (rows : Rows Key) (counts : Counts) (owner : Nat) :
    rows.foldl (fun counts row => increment counts row.2.source) counts owner =
      counts owner + occurrences rows owner := by
  induction rows generalizing counts with
  | nil => simp [occurrences, owners]
  | cons row rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      by_cases same : owner = row.2.source
      · simp [increment, occurrences, owners, same, Nat.add_assoc, Nat.add_comm]
      · simp [increment, occurrences, owners, same, Ne.symm same]

theorem admission_counts_exact {Key : Type} (rows : Rows Key) (owner : Nat) :
    admitCounts rows owner = occurrences rows owner := by
  simpa [admitCounts] using fold_counts rows (fun _ => 0) owner

/-- An indexed replacement writes at most the old/new owner's counters. The
same-owner case is included; a selected contribution proves decrement is safe. -/
def replaceCounts (counts : Counts) (oldOwner newOwner : Nat) : Counts :=
  increment (decrement counts oldOwner) newOwner

def checkedReplaceCounts (counts : Counts) (oldOwner newOwner : Nat) : Option Counts :=
  if 0 < counts oldOwner then some (replaceCounts counts oldOwner newOwner) else none

private theorem occurrences_split {Key : Type} (before suffix : Rows Key)
    (key : Key) (handle : Handle) (owner : Nat) :
    occurrences (before ++ (key, handle) :: suffix) owner =
      occurrences before owner + (if handle.source = owner then 1 else 0) +
        occurrences suffix owner := by
  by_cases same : handle.source = owner <;>
    simp [occurrences, owners, List.count_append, same] <;> omega

theorem selected_owner_positive {Key : Type} (before suffix : Rows Key)
    (key : Key) (old : Handle) :
    0 < admitCounts (before ++ (key, old) :: suffix) old.source := by
  rw [admission_counts_exact, occurrences_split]
  simp only [↓reduceIte]
  omega

theorem checked_replacement_accepted {Key : Type} (before suffix : Rows Key)
    (key : Key) (old next : Handle) :
    checkedReplaceCounts (admitCounts (before ++ (key, old) :: suffix))
      old.source next.source =
      some (replaceCounts (admitCounts (before ++ (key, old) :: suffix)) old.source next.source) := by
  simp [checkedReplaceCounts, selected_owner_positive before suffix key old]

theorem replacement_counts_exact {Key : Type} (before suffix : Rows Key)
    (key : Key) (old next : Handle) (owner : Nat) :
    replaceCounts (admitCounts (before ++ (key, old) :: suffix))
      old.source next.source owner =
        occurrences (before ++ (key, next) :: suffix) owner := by
  simp only [replaceCounts, increment, decrement, admission_counts_exact,
    occurrences_split]
  by_cases previous : owner = old.source <;> by_cases current : owner = next.source <;>
    simp_all only [eq_comm, ↓reduceIte] <;> omega

theorem replacement_other_owner_frame (counts : Counts) (oldOwner newOwner owner : Nat)
    (oldOther : owner ≠ oldOwner) (newOther : owner ≠ newOwner) :
    replaceCounts counts oldOwner newOwner owner = counts owner := by
  simp [replaceCounts, increment, decrement, oldOther, newOther]

theorem same_owner_replacement (counts : Counts) (owner query : Nat)
    (present : 0 < counts owner) : replaceCounts counts owner owner query = counts query := by
  by_cases same : query = owner
  · subst query
    simp only [replaceCounts, increment, decrement, ↓reduceIte]
    omega
  · simp [replaceCounts, increment, decrement, same]

theorem corrupt_zero_count_refused (counts : Counts) (oldOwner newOwner : Nat)
    (missing : counts oldOwner = 0) : checkedReplaceCounts counts oldOwner newOwner = none := by
  simp [checkedReplaceCounts, missing]

def dropCounts {Key : Type} (counts : Counts) (removed : Rows Key) : Counts :=
  removed.foldl (fun counts row => decrement counts row.2.source) counts

private theorem drop_counts_at {Key : Type} (rows : Rows Key) (counts : Counts) (owner : Nat) :
    dropCounts counts rows owner = counts owner - occurrences rows owner := by
  induction rows generalizing counts with
  | nil => simp [dropCounts, occurrences, owners]
  | cons row rest ih =>
      simp only [dropCounts, List.foldl_cons] at *
      rw [ih]
      by_cases same : owner = row.2.source <;>
        simp [decrement, occurrences, owners, same, eq_comm] <;> omega

/-- Apply the actual removed/added ordinal buckets. Retained rows are not
enumerated by this update. Native forks its existing index before these writes. -/
def applyDelta {Key : Type} (counts : Counts) (removed added : Rows Key) : Counts :=
  added.foldl (fun counts row => increment counts row.2.source) (dropCounts counts removed)

/-- Underflow rejection is necessary but not an ordinal-provenance proof.
The native issuer must also bind the selected distinct VIEW ordinals to the
actual source snapshot. Raw handles themselves may legitimately repeat. -/
def checkedDropCounts {Key : Type} : Counts → Rows Key → Option Counts
  | counts, [] => some counts
  | counts, row :: rest =>
      if 0 < counts row.2.source then checkedDropCounts (decrement counts row.2.source) rest
      else none

theorem checked_drop_accepted {Key : Type} (removed : Rows Key) (counts : Counts)
    (enough : ∀ owner, occurrences removed owner ≤ counts owner) :
    checkedDropCounts counts removed = some (dropCounts counts removed) := by
  induction removed generalizing counts with
  | nil => rfl
  | cons row rest ih =>
      have positive : 0 < counts row.2.source := by
        have bound := enough row.2.source
        simp [occurrences, owners] at bound
        omega
      have tail : ∀ owner, occurrences rest owner ≤ decrement counts row.2.source owner := by
        intro owner
        have bound := enough owner
        by_cases same : owner = row.2.source <;>
          simp [decrement, occurrences, owners, same, eq_comm] at bound ⊢ <;> omega
      simpa [checkedDropCounts, positive, dropCounts, List.foldl_cons] using ih _ tail

theorem batch_counts_exact {Key : Type} (kept removed added : Rows Key) (owner : Nat) :
    applyDelta (admitCounts (kept ++ removed)) removed added owner =
      occurrences (kept ++ added) owner := by
  rw [applyDelta, fold_counts, drop_counts_at, admission_counts_exact]
  simp [occurrences, owners, List.count_append]

theorem batch_other_owner_frame {Key : Type} (counts : Counts) (removed added : Rows Key)
    (owner : Nat) (notRemoved : owner ∉ owners removed) (notAdded : owner ∉ owners added) :
    applyDelta counts removed added owner = counts owner := by
  rw [applyDelta, fold_counts, drop_counts_at]
  simp [occurrences, List.count_eq_zero_of_not_mem notRemoved,
    List.count_eq_zero_of_not_mem notAdded]

/-- A reference for prototype-map-put's FIRST indexed contribution, preserving
later duplicate-key contributions. Native uses its existing first ordinal. -/
def put {Key : Type} [DecidableEq Key] (key : Key) (next : Handle) : Rows Key → Rows Key
  | [] => [(key, next)]
  | row :: rest => if row.1 = key then (key, next) :: rest else row :: put key next rest

theorem put_at_first_ordinal {Key : Type} [DecidableEq Key]
    (before suffix : Rows Key) (key : Key) (old next : Handle)
    (first : ∀ row ∈ before, row.1 ≠ key) :
    put key next (before ++ (key, old) :: suffix) = before ++ (key, next) :: suffix := by
  induction before with
  | nil => simp [put]
  | cons row rest ih =>
      have other := first row (by simp)
      have tail : ∀ item ∈ rest, item.1 ≠ key :=
        fun item member => first item (List.mem_cons_of_mem _ member)
      simpa [put, other] using congrArg (List.cons row) (ih tail)

theorem put_preserves_later_duplicate {Key : Type} [DecidableEq Key]
    (key : Key) (first later next : Handle) (suffix : Rows Key) :
    put key next ((key, first) :: (key, later) :: suffix) =
      (key, next) :: (key, later) :: suffix := by simp [put]

abbrev Registered (counts : Counts) (owner : Nat) : Prop := 0 < counts owner

theorem replacement_registration_exact {Key : Type} (before suffix : Rows Key)
    (key : Key) (old next : Handle) (owner : Nat) :
    Registered (replaceCounts (admitCounts (before ++ (key, old) :: suffix))
      old.source next.source) owner ↔
      owner = next.source ∨ Registered (admitCounts (before ++ suffix)) owner := by
  rw [Registered, replacement_counts_exact]
  simp only [occurrences_split, Registered, admission_counts_exact]
  by_cases same : next.source = owner <;>
    simp [same, Eq.symm, occurrences, owners, List.count_append] <;> omega

/-- This frontier is a semantic specification of the existing registration
index's positive keys, not an eraseDups pass to run after every native clone. -/
def frontier {Key : Type} (rows : Rows Key) : List Nat := (owners rows).eraseDups

theorem frontier_exact {Key : Type} (rows : Rows Key) (owner : Nat) :
    owner ∈ frontier rows ↔ Registered (admitCounts rows) owner := by
  simp [frontier, Registered, admission_counts_exact, occurrences, List.count_pos_iff]

private def duplicateRows : Rows Nat := [(7, ⟨0, 0⟩), (7, ⟨0, 1⟩)]

/-- Dropping all contributions by key loses the old storage owner even though
the visible key is still present. The native first-ordinal operation retains it. -/
theorem duplicate_key_is_not_owner_retirement :
    Registered (admitCounts (put 7 ⟨1, 0⟩ duplicateRows)) 0 ∧
    ¬ Registered (admitCounts [(7, (⟨1, 0⟩ : Handle))]) 0 := by
  decide

/-- Counts cannot authenticate which ordinals were removed: removing the SAME
view ordinal twice can pass the owner multiplicity guard. An issued exact cut
and distinct view ordinals remain mandatory even when this guard succeeds. -/
theorem duplicate_ordinal_is_not_authenticated_by_counts :
    let source : Rows Nat := [(7, ⟨0, 0⟩), (8, ⟨0, 1⟩)]
    let removed : Rows Nat := [(7, ⟨0, 0⟩), (7, ⟨0, 0⟩)]
    ∃ after, checkedDropCounts (admitCounts source) removed = some after ∧
      after 0 = 0 ∧ ¬ ([0, 0] : List Nat).Nodup := by
  dsimp only
  refine ⟨_, rfl, ?_, ?_⟩ <;> decide

/-- Eligibility projects only registered raw owners. Bounds, constructor/writer
coverage and exact native source provenance remain separate admission duties. -/
def Eligible {Self Value : Type} (storage : Storage Self Value) (counts : Counts) : Prop :=
  ∀ owner, Registered counts owner → (View.issue storage ⟨0, owner⟩).isSome = true

theorem exposure_fences_registered_view {Self Value : Type}
    (storage next : Storage Self Value) (counts : Counts) (view : View)
    (index : Nat) (handle : Handle) (registered : Registered counts view.owner)
    (step : View.expose storage view index = some (next, handle)) :
    ¬ Eligible next counts := by
  intro eligible
  have revoked := View.exposure_revokes_alias_issuance storage next view ⟨0, view.owner⟩
    index handle rfl step
  have live := eligible view.owner registered
  simp [revoked] at live

theorem exposure_unregistered_frame {Self Value : Type}
    (storage next : Storage Self Value) (counts : Counts) (view : View)
    (index : Nat) (handle : Handle) (absent : ¬ Registered counts view.owner)
    (step : View.expose storage view index = some (next, handle)) :
    Eligible next counts ↔ Eligible storage counts := by
  have frame (owner : Nat) (registered : Registered counts owner) :
      View.issue next ⟨0, owner⟩ = View.issue storage ⟨0, owner⟩ := by
    apply View.exposure_other_owner_frame storage next view ⟨0, owner⟩ index handle _ step
    intro same
    exact absent (same ▸ registered)
  constructor <;> intro eligible owner registered
  · rw [← frame owner registered]
    exact eligible owner registered
  · rw [frame owner registered]
    exact eligible owner registered

open LeanPoo.Functional.StrongComponents

/-- Existing Graph adjacency plus the new source-registration part of a row.
ownerAt is the admitted native key/ordinal map, not a Module/package identity. -/
def edges {n : Nat} (fixed : Fin n → Fin n → Bool) (ownerAt : Fin n → Nat)
    (counts : Fin n → Counts) (consumer provider : Fin n) : Bool :=
  fixed consumer provider || decide (Registered (counts consumer) (ownerAt provider))

def replaceRow {n : Nat} (counts : Fin n → Counts) (consumer : Fin n)
    (replacement : Counts) : Fin n → Counts :=
  fun query => if query = consumer then replacement else counts query

/-- Feed the existing old-inverse theorem the DERIVED row frame. Mark the
edited consumer even when its provider set happens to stay equal. Additional
changed source owners join the same roots; no second graph traversal is added. -/
theorem old_inverse_closure_exact {n : Nat}
    (fixed : Fin n → Fin n → Bool) (ownerAt : Fin n → Nat)
    (counts : Fin n → Counts) (consumer : Fin n) (replacement : Counts)
    (changed : Fin n → Bool) (reader : Fin n) :
    let roots := fun node => decide (node = consumer) || changed node
    (∃ root, roots root = true ∧ Reach (edges fixed ownerAt counts) reader root) ↔
      ∃ root, roots root = true ∧
        Reach (edges fixed ownerAt (replaceRow counts consumer replacement)) reader root := by
  dsimp only
  apply edited_root_closure_exact
  intro node clean provider
  have other : node ≠ consumer := by
    intro same
    simp [same] at clean
  simp [edges, replaceRow, other]

open LeanPoo.Functional.ComponentPublication

def captureStamp (versions : Nat → Nat) (registered : List Nat) : List (Nat × Nat) :=
  registered.map fun owner => (owner, versions owner)

theorem registered_exposure_changes_stamp (versions : Nat → Nat)
    (registered : List Nat) (owner : Nat) (member : owner ∈ registered) :
    captureStamp versions registered ≠ captureStamp (advanceFamily versions owner) registered := by
  intro same
  have selected := (List.map_inj_left.mp same) owner member
  have revision := congrArg Prod.snd selected
  simp [advanceFamily] at revision

/-- Source exposure during admission rejects the staged result even if its
publication head is unchanged. Drift is DERIVED from the exact owner frontier,
not assumed as an unrelated caller-supplied stale flag. -/
theorem exposure_rejects_pending_capture {Key : Type}
    (expected current candidate : Published) (versions : Nat → Nat)
    (rows : Rows Key) (owner : Nat) (approved : Bool)
    (registered : Registered (admitCounts rows) owner) :
    installChecked expected current candidate (captureStamp versions (frontier rows))
      (captureStamp (advanceFamily versions owner) (frontier rows)) approved =
        ⟨current, false⟩ := by
  apply metadata_stale
  exact registered_exposure_changes_stamp versions (frontier rows) owner
    ((frontier_exact rows owner).mpr registered)

theorem unrelated_exposure_keeps_stamp (versions : Nat → Nat)
    (registered : List Nat) (owner : Nat) (absent : owner ∉ registered) :
    captureStamp (advanceFamily versions owner) registered = captureStamp versions registered := by
  apply List.map_inj_left.mpr
  intro other member
  have separate : other ≠ owner := by
    intro same
    exact absent (same ▸ member)
  simp [advanceFamily, separate]

end LeanPoo.Object.SourceViews
