import Std

namespace GraphForwardRows

variable {K E : Type}

abbrev Rows (K : Type) := K → Option (List K)

-- An empty row is absent in the sparse backing map, but not absent in the
-- schedule domain. Both reads return none for an unsupported owner.
def sparse (rows : Rows K) (key : K) : Option (List K) :=
  (rows key).filter (! ·.isEmpty)

def supportedRead (support : K → Bool) (rows : Rows K) (key : K) : Option (List K) :=
  if support key then some ((rows key).getD []) else none

def ExactSupport (support : K → Bool) (rows : Rows K) : Prop :=
  ∀ k, support k = (rows k).isSome

theorem cold_base_exact (support : K → Bool) (rows : Rows K)
    (exact : ExactSupport support rows) : supportedRead support (sparse rows) = rows := by
  funext k
  have h := exact k
  cases hk : rows k with
  | none => simp [supportedRead, hk] at h ⊢; simp [h]
  | some row =>
    have yes : support k = true := by simpa [hk] using h
    cases row <;> simp [supportedRead, sparse, hk, yes, Option.filter]

-- Outer none is no patch. Some none is Scheme #f (retired), not [].
abbrev Changes (K : Type) := K → Option (Option (List K))

def patched (base : Rows K) (changes : Changes K) (key : K) : Option (List K) :=
  (changes key).getD (base key)

def write [DecidableEq K] (changes : Changes K) (key : K) (row : Option (List K)) : Changes K :=
  fun k => if k = key then some row else changes k

def overlay [DecidableEq K] (batch : List (K × Option (List K)))
    (changes : Changes K) : Changes K :=
  batch.foldl (fun acc (key, row) => write acc key row) changes

theorem revised_rows_exact [DecidableEq K] (support : K → Bool) (rows : Rows K)
    (changes : Changes K) (exact : ExactSupport support rows) (batch : List (K × Option (List K))) :
    patched (supportedRead support (sparse rows)) (overlay batch changes) =
      patched rows (overlay batch changes) := by
  rw [cold_base_exact support rows exact]

theorem empty_patch_masks_base [DecidableEq K] (base : Rows K) (changes : Changes K) (key : K) :
    patched base (write changes key (some [])) key = some [] := by
  simp [patched, write]

theorem no_unsupported_as_empty (support : K → Bool) (rows : Rows K) (key : K)
    (h : support key = false) : supportedRead support rows key = none := by
  simp [supportedRead, h]

-- The private cold table starts empty. A single pass stores only nonempty
-- rows; there is no dense intermediate map. The admitted roster is unique.
def lookup [DecidableEq K] : List (K × List K) → Rows K
  | [], _ => none
  | (k, row) :: rest, query => if query = k then some row else lookup rest query

theorem lookup_missing [DecidableEq K] (entries : List (K × List K)) (key : K)
    (absent : key ∉ entries.map Prod.fst) : lookup entries key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, row⟩ := entry
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp [lookup, absent.1, ih absent.2]

def materialized [DecidableEq K] (entries : List (K × List K)) : Rows K :=
  lookup (entries.filter (! ·.2.isEmpty))

theorem materialized_exact [DecidableEq K] (entries : List (K × List K))
    (unique : (entries.map Prod.fst).Nodup) : materialized entries = sparse (lookup entries) := by
  funext key
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, row⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at unique
    have tail := ih unique.2
    by_cases atKey : key = k
    · subst key
      cases row with
      | nil => simpa [materialized, lookup, sparse, Option.filter, lookup_missing rest k unique.1]
          using tail
      | cons a restRow => simp [materialized, lookup, sparse, Option.filter]
    · cases row with
      | nil => simpa [materialized, lookup, sparse, atKey] using tail
      | cons a restRow => simpa [materialized, lookup, sparse, atKey] using tail

theorem fused_cold_exact [DecidableEq K] (entries : List (K × List K))
    (unique : (entries.map Prod.fst).Nodup) (support : K → Bool)
    (exact : ExactSupport support (lookup entries)) :
    supportedRead support (materialized entries) = lookup entries := by
  rw [materialized_exact entries unique, cold_base_exact support (lookup entries) exact]

-- Without unique owners, dropping an empty row can reveal a different row.
example : materialized [(0, []), (0, [1])] 0 ≠ sparse (lookup [(0, []), (0, [1])]) 0 := by
  decide

theorem retirement_masks_base [DecidableEq K] (base : Rows K) (changes : Changes K) (key : K) :
    patched base (write changes key none) key = none := by
  simp [patched, write]

theorem patch_leaves_other_owner [DecidableEq K] (base : Rows K) (changes : Changes K)
    (key other : K) (row : Option (List K)) (different : other ≠ key) :
    patched base (write changes key row) other = patched base changes other := by
  simp [patched, write, different]

-- A blanket empty default loses the distinction even before any edit.
example : (supportedRead (fun _ => false) (fun _ => none) 0 : Option (List Nat)) ≠ some [] := by
  decide

-- After remove/re-add the base may still contain the original outgoing edges.
example : patched (fun _ => some [1]) (write (write (fun _ => none) 0 none) 0 (some [])) 0 =
    some ([] : List Nat) := by decide

-- Capture is outside the representation rewrite. In particular an error
-- remains the same error and never runs the continuation. Events include
-- the independent validation, constructor and author effect boundaries.
def afterCapture (capture : Except E (Rows K) × List Event)
    (next : Rows K → Except E A) : Except E A × List Event :=
  (capture.1 >>= next, capture.2)

theorem same_captured_observation (support : K → Bool)
    (capture : Except E (Rows K) × List Event) (next : Rows K → Except E A)
    (exact : ∀ rows, capture.1 = .ok rows → ExactSupport support rows) :
    afterCapture capture (fun rows => next (supportedRead support (sparse rows))) =
      afterCapture capture next := by
  rcases capture with ⟨result, events⟩
  cases result with
  | error e => rfl
  | ok rows =>
    have h := cold_base_exact support rows (exact rows rfl)
    simp [afterCapture, Bind.bind, Except.bind, h]

-- The storage policy saves writes, not the traversal needed to inspect rows.
def nonempty (rows : List (List K)) : List (List K) := rows.filter (! ·.isEmpty)

theorem stores_at_most (rows : List (List K)) : (nonempty rows).length ≤ rows.length :=
  List.length_filter_le _ _

theorem no_cold_writes_when_empty (rows : List (List K))
    (h : ∀ row ∈ rows, row = []) : nonempty rows = [] := by
  simpa [nonempty] using h

-- In schedule-owned the author program getters are already finished before
-- schedule-rows. A missing captured program contributes an empty row, and
-- an explicit captured program contributes its stored ordered footprint.
def ownedRow (captured : Rows K) (key : K) : List K := (captured key).getD []

def ownedBase (support : K → Bool) (captured : Rows K) : Rows K :=
  fun key => if support key then some (ownedRow captured key) else none

theorem empty_capture_base_exact (support : K → Bool) (captured : Rows K)
    (empty : ∀ key, captured key = none) :
    ownedBase support captured = supportedRead support (fun _ => none) := by
  funext k
  simp [ownedBase, ownedRow, supportedRead, empty]

theorem all_authored_rows_empty (captured : Rows K)
    (noEdges : ∀ key row, captured key = some row → row = []) :
    ∀ key, ownedRow captured key = [] := by
  intro key
  cases h : captured key with
  | none => simp [ownedRow, h]
  | some row => simp [ownedRow, h, noEdges key row h]

-- A sealed program view returns a defensive copy of the stored row.
-- Lean lists already have value semantics.
def rowsThroughView (keys : List K) (program : K → Option P)
    (row : P → List K) : List (K × List K) :=
  keys.map fun key => (key, ((program key).map row).getD [])

def rowsFromStore (keys : List K) (program : K → Option P)
    (row : P → List K) : List (K × List K) :=
  keys.map fun key => (key, match program key with
    | none => []
    | some entry => row entry)

theorem sealed_rows_exact (keys : List K) (program : K → Option P)
    (row : P → List K) : rowsThroughView keys program row =
      rowsFromStore keys program row := by
  unfold rowsThroughView rowsFromStore
  apply List.map_congr_left
  intro key _
  cases program key <;> rfl

-- Source admission, the body, and the independent recheck use the same
-- operations. Events can include the full observed effect trace.
def prepareSealed (observe : Except E (List K × (K → Option P)) × List Event)
    (rows : List K → (K → Option P) → List (K × List K))
    (finish : List (K × List K) → Except E A)
    (recheck : A → Except E A) : Except E A × List Event :=
  (observe.1 >>= fun (keys, program) => finish (rows keys program) >>= recheck,
   observe.2)

theorem sealed_row_handoff_exact
    (observe : Except E (List K × (K → Option P)) × List Event)
    (row : P → List K) (finish : List (K × List K) → Except E A)
    (recheck : A → Except E A) :
    prepareSealed observe (fun keys program => rowsThroughView keys program row) finish recheck =
    prepareSealed observe (fun keys program => rowsFromStore keys program row) finish recheck := by
  have same : (fun keys program => rowsThroughView keys program row) =
      (fun keys program => rowsFromStore keys program row) := by
    funext keys program
    exact sealed_rows_exact keys program row
  rw [same]

#print axioms sealed_row_handoff_exact
#print axioms cold_base_exact
#print axioms fused_cold_exact
#print axioms revised_rows_exact
#print axioms same_captured_observation
#print axioms no_cold_writes_when_empty

end GraphForwardRows
