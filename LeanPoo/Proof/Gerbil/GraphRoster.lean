import Std

namespace GraphRoster
variable {K : Type} [DecidableEq K]

-- K is the already validated symbol-identity domain. This algorithm does not
-- replace proper-list/symbol validation, constructor effects or author checks.
abbrev Membership (K : Type) := K → Bool
def empty : Membership K := fun _ => false
def mark (seen : Membership K) (key : K) : Membership K :=
  fun query => if query = key then true else seen query

-- Current first-occurrence normalization, followed by a separate support pass.
def firsts : List K → Membership K → List K
  | [], _ => []
  | key :: rest, seen =>
      if seen key then firsts rest seen else key :: firsts rest (mark seen key)

def twoPass (keys : List K) : List K × Membership K :=
  let names := firsts keys empty
  (names, fun query => decide (query ∈ names))

-- Proposed one-pass state transition, returning BOTH admitted observations.
def admit : List K → Membership K → List K × Membership K
  | [], seen => ([], seen)
  | key :: rest, seen =>
      if seen key then admit rest seen
      else let next := admit rest (mark seen key)
           (key :: next.1, next.2)

theorem same_order (keys : List K) (seen : Membership K) :
    (admit keys seen).1 = firsts keys seen := by
  induction keys generalizing seen with
  | nil => rfl
  | cons key rest ih =>
    cases h : seen key <;> simp [admit, firsts, h, ih]

theorem final_membership (keys : List K) (seen : Membership K) (query : K) :
    (admit keys seen).2 query = (seen query || decide (query ∈ keys)) := by
  induction keys generalizing seen with
  | nil => simp [admit]
  | cons key rest ih =>
    by_cases eq : query = key
    · subst query
      cases h : seen key <;> simp [admit, mark, h, ih]
    · cases h : seen key <;> simp [admit, mark, h, ih, eq]

theorem firsts_membership (keys : List K) (seen : Membership K) (query : K) :
    query ∈ firsts keys seen ↔ query ∈ keys ∧ seen query = false := by
  induction keys generalizing seen with
  | nil => simp [firsts]
  | cons key rest ih =>
    by_cases eq : query = key
    · subst query
      cases h : seen key <;> simp [firsts, mark, h, ih]
    · cases h : seen key <;> simp [firsts, mark, h, ih, eq]

theorem firsts_unique (keys : List K) (seen : Membership K) :
    (firsts keys seen).Nodup := by
  induction keys generalizing seen with
  | nil => simp [firsts]
  | cons key rest ih =>
    cases h : seen key
    · simp only [firsts, h, Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      constructor
      · simp [firsts_membership, mark]
      · exact ih _
    · simpa [firsts, h] using ih seen

theorem one_pass_exact (keys : List K) : admit keys empty = twoPass keys := by
  apply Prod.ext
  · exact same_order keys empty
  · funext query
    rw [final_membership]
    simp only [empty, Bool.false_or, twoPass]
    congr 1
    exact propext (firsts_membership keys empty query |>.trans (by simp [empty])) |>.symm

-- Validation stays before normalization. Its error payload is opaque here:
-- this theorem cannot authorize a different native validator or refusal order.
def checked {E : Type} (normalize : List K → List K × Membership K)
    (validated : Except E (List K)) : Except E (List K × Membership K) :=
  validated.map normalize

theorem checked_exact {E : Type} (validated : Except E (List K)) :
    checked (fun keys => admit keys empty) validated =
      checked twoPass validated := by
  cases validated with
  | error reason => rfl
  | ok keys => simp [checked, one_pass_exact]

-- A downstream computation may inspect order and membership, or fail. Equal
-- inputs preserve it, provided effectful construction/checks stay external.
theorem continuation_exact {E R : Type} (validated : Except E (List K))
    (next : Except E (List K × Membership K) → R) :
    next (checked (fun keys => admit keys empty) validated) =
      next (checked twoPass validated) := by
  rw [checked_exact]

-- Persistent mathematical state never alters an older membership function.
-- Scheme's mutable-table implementation still owes a separate ownership proof.
theorem mark_other (seen : Membership K) (key query : K) (different : query ≠ key) :
    mark seen key query = seen query := by
  simp [mark, different]

-- Matching the returned roster is insufficient if native constructors expose
-- different effects. Trace equality is an explicit, necessary obligation.
theorem with_trace_exact {Event : Type} (keys : List K)
    (oldTrace newTrace : List Event) (effects : newTrace = oldTrace) :
    (admit keys empty, newTrace) = (twoPass keys, oldTrace) := by
  rw [one_pass_exact, effects]

theorem trace_mismatch_rejects {Event : Type} (keys : List K)
    (oldTrace newTrace : List Event) (different : newTrace ≠ oldTrace) :
    (admit keys empty, newTrace) ≠ (twoPass keys, oldTrace) := by
  intro equal
  exact different (congrArg Prod.snd equal)

-- Refinement for the existing native deduplicator, independent of its table
-- representation. These laws must hold for all intermediate private states.
def normalizeTable {S : Type} (has : S → K → Bool) (put : S → K → S) :
    List K → S → List K × S
  | [], state => ([], state)
  | key :: rest, state =>
      if has state key then normalizeTable has put rest state
      else let next := normalizeTable has put rest (put state key)
           (key :: next.1, next.2)

theorem table_refinement {S : Type} (has : S → K → Bool) (put : S → K → S)
    (put_law : ∀ state key query,
      has (put state key) query = if query = key then true else has state query)
    (keys : List K) (state : S) :
    ((normalizeTable has put keys state).1,
      has (normalizeTable has put keys state).2) = admit keys (has state) := by
  induction keys generalizing state with
  | nil => rfl
  | cons key rest ih =>
    have marked : has (put state key) = mark (has state) key := by
      funext query
      exact put_law state key query
    cases h : has state key
    · simp only [normalizeTable, admit, h, Bool.false_eq_true, ↓reduceIte]
      have step := ih (put state key)
      rw [marked] at step
      have order := congrArg Prod.fst step
      have domain := congrArg Prod.snd step
      exact Prod.ext (congrArg (List.cons key) order) domain
    · simpa [normalizeTable, admit, h] using ih state

theorem native_normalization_order {S : Type} (has : S → K → Bool)
    (put : S → K → S)
    (put_law : ∀ state key query,
      has (put state key) query = if query = key then true else has state query)
    (keys : List K) (initial : S) (empty_law : has initial = empty) :
    (normalizeTable has put keys initial).1 = firsts keys empty := by
  have same := congrArg Prod.fst (table_refinement has put put_law keys initial)
  simpa only [empty_law, same_order] using same

-- Count abstract table operations, NOT CPU/GC or an assumed O(1) hash cost.
def admissionWork : List K → Membership K → Nat × Nat
  | [], _ => (0, 0)
  | key :: rest, seen =>
      if seen key then
        let next := admissionWork rest seen
        (next.1 + 1, next.2)
      else
        let next := admissionWork rest (mark seen key)
        (next.1 + 1, next.2 + 1)

theorem probes_exact (keys : List K) (seen : Membership K) :
    (admissionWork keys seen).1 = keys.length := by
  induction keys generalizing seen with
  | nil => rfl
  | cons key rest ih =>
    cases h : seen key <;> simp [admissionWork, h, ih]

theorem inserts_exact (keys : List K) (seen : Membership K) :
    (admissionWork keys seen).2 = (firsts keys seen).length := by
  induction keys generalizing seen with
  | nil => rfl
  | cons key rest ih =>
    cases h : seen key <;> simp [admissionWork, firsts, h, ih]

-- A new identity at the unread tail changes the required support result.
-- This does not assert a machine-time lower bound or cost of hashing.
theorem fresh_tail_changes_support (keys : List K) (fresh : K)
    (absent : fresh ∉ keys) :
    (admit keys empty).2 fresh = false ∧
      (admit (keys ++ [fresh]) empty).2 fresh = true := by
  simp [final_membership, empty, absent]

/-- Membership edits probe the complete predecessor support. A source-bound
index may answer those probes without rebuilding a second membership table. -/
def membershipAdmitted (supports : Membership K) (added removed : List K) : Bool :=
  added.all (fun key => !supports key) && removed.all supports

theorem membership_preflight_exact (keys added removed : List K)
    (supports : Membership K)
    (bound : ∀ key, supports key = decide (key ∈ keys)) :
    membershipAdmitted supports added removed =
      membershipAdmitted (fun key => decide (key ∈ keys)) added removed := by
  have same : supports = (fun key => decide (key ∈ keys)) := funext bound
  rw [same]

-- The explicit output walks the position vector from its end, consing each
-- position in front of the suffix already emitted.
def emitPositionList (positions suffix : List K) : List K :=
  positions.reverse.foldl (fun out key => key :: out) suffix

omit [DecidableEq K] in
theorem emit_position_list_exact (positions suffix : List K) :
    emitPositionList positions suffix = positions ++ suffix := by
  induction positions generalizing suffix with
  | nil => rfl
  | cons key rest ih =>
    simp [emitPositionList, List.reverse_cons, List.foldl_append,
      show rest.reverse.foldl (fun out key => key :: out) suffix = rest ++ suffix from ih suffix]

#print axioms emit_position_list_exact
#print axioms same_order
#print axioms final_membership
#print axioms firsts_membership
#print axioms firsts_unique
#print axioms one_pass_exact
#print axioms checked_exact
#print axioms continuation_exact
#print axioms mark_other
#print axioms with_trace_exact
#print axioms trace_mismatch_rejects
#print axioms table_refinement
#print axioms native_normalization_order
#print axioms probes_exact
#print axioms inserts_exact
#print axioms fresh_tail_changes_support
end GraphRoster
