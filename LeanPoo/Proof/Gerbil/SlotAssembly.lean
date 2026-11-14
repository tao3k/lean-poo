import Std

namespace SlotAssembly

-- Opaque values include already compiled receiver-bound closures. Keys denote
-- identities, never printed names. This is an observation model of the existing
-- hash store, not a proposed Scheme association-list representation.
abbrev Store (V : Type) := Nat → Option V

def put (store : Store V) (key : Nat) (value : V) : Store V :=
  fun query => if query = key then some value else store query

def install : List (Nat × V) → Store V → Store V
  | [], store => store
  | (key, value) :: rest, store => install rest (put store key value)

def enumerate (keys : List Nat) (store : Store V) :=
  keys.map (fun key => (key, store key))

theorem outside_unchanged (rows : List (Nat × V)) (store : Store V) (query : Nat)
    (outside : query ∉ rows.map Prod.fst) : install rows store query = store query := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at outside
    rw [install, ih _ outside.2]
    simp [put, outside.1]

-- Native enumeration is unique. Without uniqueness, a later overwrite could
-- replace a value captured earlier, even if physical key order did not move.
theorem installed_snapshot (rows : List (Nat × V)) (store : Store V)
    (unique : (rows.map Prod.fst).Nodup) :
    enumerate (rows.map Prod.fst) (install rows store) =
      rows.map (fun row => (row.1, some row.2)) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rest ih =>
    have distinct : row.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa using unique
    change (row.1, install rest (put store row.1 row.2) row.1) ::
      enumerate (rest.map Prod.fst) (install rest (put store row.1 row.2)) = _
    rw [outside_unchanged _ _ _ distinct.1, ih _ distinct.2]
    simp [put]

-- Preparation retains the exact first refused owner and successfully compiled
-- prefix. Thus a failed candidate also has the same private partial writes.
def prepare (compile : Nat → S → Except E V) :
    List (Nat × S) → Except (Nat × E) Unit × List (Nat × V)
  | [] => (.ok (), [])
  | (key, spec) :: rest =>
      match compile key spec with
      | .error cause => (.error (key, cause), [])
      | .ok value =>
          let (status, built) := prepare compile rest
          (status, (key, value) :: built)

theorem prepared_keys (compile : Nat → S → Except E V) (rows : List (Nat × S))
    (success : (prepare compile rows).1 = .ok ()) :
    ((prepare compile rows).2.map Prod.fst) = rows.map Prod.fst := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases step : compile row.1 row.2 with
    | error cause => simp [prepare, step] at success
    | ok value =>
      have tail : (prepare compile rest).1 = .ok () := by
        simpa [prepare, step] using success
      simpa [prepare, step] using congrArg (List.cons row.1) (ih tail)

def original (compile : Nat → S → Except E V) (rows : List (Nat × S))
    (store : Store V) : Except (Nat × E) (List (Nat × Option V)) × Store V :=
  let (status, built) := prepare compile rows
  let final := install built store
  (status.map (fun _ => enumerate (rows.map Prod.fst) final), final)

def fused (compile : Nat → S → Except E V) (rows : List (Nat × S))
    (store : Store V) : Except (Nat × E) (List (Nat × Option V)) × Store V :=
  let (status, built) := prepare compile rows
  (status.map (fun _ => built.map (fun row => (row.1, some row.2))), install built store)

theorem complete_exact (compile : Nat → S → Except E V) (rows : List (Nat × S))
    (store : Store V) (unique : (rows.map Prod.fst).Nodup) :
    fused compile rows store = original compile rows store := by
  cases status : (prepare compile rows).1 with
  | error cause => simp [original, fused, status, Except.map]
  | ok result =>
    cases result
    have keys := prepared_keys compile rows status
    have distinct : ((prepare compile rows).2.map Prod.fst).Nodup := by
      simpa [keys] using unique
    have snapshot := installed_snapshot (prepare compile rows).2 store distinct
    rw [keys] at snapshot
    simp [original, fused, status, snapshot]

-- Hooks receive the complete frozen snapshot, never an interleaved partial
-- catalog. Their effects and failures may be arbitrary AFTER this pure interval.
theorem arbitrary_continuation_exact (compile : Nat → S → Except E V)
    (rows : List (Nat × S)) (store : Store V) (unique : (rows.map Prod.fst).Nodup)
    (next : (Except (Nat × E) (List (Nat × Option V)) × Store V) → R) :
    next (fused compile rows store) = next (original compile rows store) := by
  rw [complete_exact compile rows store unique]

structure Layout where
  keys : List Nat
  free : Nat
  width : Nat
  deriving DecidableEq, Repr

abbrev needsRehash (layout : Layout) := layout.free < layout.width / 4

-- An existing-key native replacement preserves free/capacity and key positions
-- ONLY if its pre-write rehash branch is not taken. Rehash layout is unconstrained.
def existingWrite (rehash : Layout → Layout) (layout : Layout) : Layout :=
  if needsRehash layout then rehash layout else layout

theorem no_rehash_interval (rehash : Layout → Layout) (layout : Layout)
    (room : layout.width / 4 ≤ layout.free) (count : Nat) :
    (List.replicate count ()).foldl (fun state _ => existingWrite rehash state) layout = layout := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    have stable : existingWrite rehash layout = layout := by
      simp [existingWrite, needsRehash, Nat.not_lt.mpr room]
    rw [stable]
    exact ih

example : needsRehash ⟨[1, 2], 0, 8⟩ := by decide
example : (existingWrite (fun layout => { layout with keys := layout.keys.reverse })
    ⟨[1, 2], 0, 8⟩).keys = [2, 1] := by decide
example : enumerate [0] (install [(0, false)] (fun _ => none)) = [(0, some false)] := rfl
example : enumerate [1, 2] (install [(1, 7), (1, 9)] (fun _ => none)) ≠
    [(1, some 7), (1, some 9)] := by decide

#print axioms installed_snapshot
#print axioms prepared_keys
#print axioms complete_exact
#print axioms arbitrary_continuation_exact
#print axioms no_rehash_interval

end SlotAssembly
