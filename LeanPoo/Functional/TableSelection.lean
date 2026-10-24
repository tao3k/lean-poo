import LeanPoo.Functional.SetStyle

/-! Checked selection is a finite future-work extension. Backend folds preserve
admitted binding identities; effectful predicates may refuse. The ownership model
stages both results before committing once. It does not roll back callback effects,
prove Gerbil allocation, or assert exclusive ownership of persistent tree nodes. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Visit each admitted entry once in fold order; the first refusal stops selection.
Bool is the accepted predicate codomain, never general truthiness. -/
def selectBindings (classify : A → Except E Bool) : List A → Except E (List A × List A)
  | [] => .ok ([], [])
  | entry :: rest =>
    match classify entry with
    | .error cause => .error cause
    | .ok selected =>
      match selectBindings classify rest with
      | .error cause => .error cause
      | .ok (yes, no) => .ok (if selected then (entry :: yes, no) else (yes, entry :: no))

/-- Successful selection neither loses nor invents entries (including Functions).
The statement uses membership, so repeated entries need no equality test. -/
theorem selectBindings_coverage (classify : A → Except E Bool) (rows yes no : List A)
    (success : selectBindings classify rows = .ok (yes, no)) (entry : A) :
    entry ∈ yes ∨ entry ∈ no ↔ entry ∈ rows := by
  induction rows generalizing yes no with
  | nil =>
    simp [selectBindings] at success
    rcases success with ⟨rfl, rfl⟩
    simp
  | cons head tail ih =>
    simp only [selectBindings] at success
    cases hc : classify head with
    | error cause => simp [hc] at success
    | ok chosen =>
      cases ht : selectBindings classify tail with
      | error cause => simp [hc, ht] at success
      | ok branches =>
        rcases branches with ⟨left, right⟩
        have covered := ih left right ht
        cases chosen <;> simp [hc, ht] at success
        all_goals
          rcases success with ⟨rfl, rfl⟩
          simpa only [List.mem_cons, or_assoc, or_left_comm] using
            (or_congr (Iff.rfl (a := entry = head)) covered)

/-- Even with duplicate entries, successful selection preserves multiplicity in
aggregate: no admission step may silently drop a binding. -/
theorem selectBindings_length (classify : A → Except E Bool) (rows yes no : List A)
    (success : selectBindings classify rows = .ok (yes, no)) :
    yes.length + no.length = rows.length := by
  induction rows generalizing yes no with
  | nil =>
    simp [selectBindings] at success
    rcases success with ⟨rfl, rfl⟩
    rfl
  | cons head tail ih =>
    simp only [selectBindings] at success
    cases hc : classify head with
    | error cause => simp [hc] at success
    | ok chosen =>
      cases ht : selectBindings classify tail with
      | error cause => simp [hc, ht] at success
      | ok branches =>
        rcases branches with ⟨left, right⟩
        have counted := ih left right ht
        cases chosen <;> simp [hc, ht] at success
        all_goals
          rcases success with ⟨rfl, rfl⟩
          simp only [List.length_cons]
          omega

/-- Refusal stops at the first classifier error; no partial roots are returned. -/
theorem selectBindings_head_refused (classify : A → Except E Bool) (head : A)
    (tail : List A) (cause : E) (refused : classify head = .error cause) :
    selectBindings classify (head :: tail) = .error cause := by
  simp [selectBindings, refused]

/-- A total classifier agrees with stable list filtering on both sides. -/
theorem selectBindings_total (classify : A → Bool) (rows : List A) :
    selectBindings (E := E) (fun entry => .ok (classify entry)) rows =
      .ok (rows.filter classify, rows.filter (fun entry => !classify entry)) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    cases hc : classify head <;> simp [selectBindings, ih, hc]

/-- Stage the complete pair before reusing the existing single-owner installer.
Mutable keeps the first root at its old identity; the second capability is fresh.
Linear consumes the old owner once; pure and posh retain the predecessor. -/
def stylePartition (style : TableStyle) (state : Option A)
    (prepare : A → Except E (A × A)) : Option A × Except (StyleFailure E) (A × A) :=
  match state with
  | none => (none, .error .consumed)
  | some before =>
    match prepare before with
    | .error cause => (state, .error (.callback cause))
    | .ok roots =>
      let installed := styleStep (E := E) style state (fun _ => .ok roots.1)
      (installed.1, .ok roots)

/-- Either branch's admission failure preserves the old owner and exact cause. -/
theorem stylePartition_refused (style : TableStyle) (before : A)
    (prepare : A → Except E (A × A)) (cause : E)
    (refused : prepare before = .error cause) :
    stylePartition style (some before) prepare = (some before, .error (.callback cause)) := by
  simp [stylePartition, refused]

/-- A consumed input cannot run a predicate or revive a result capability. -/
theorem stylePartition_consumed (style : TableStyle) (prepare : A → Except E (A × A)) :
    stylePartition style none prepare = (none, .error .consumed) := rfl

/-- All ownership presentations expose exactly the same prepared roots. -/
theorem stylePartition_observation (style : TableStyle) (before yes no : A)
    (prepare : A → Except E (A × A)) (ready : prepare before = .ok (yes, no)) :
    (stylePartition style (some before) prepare).2 = .ok (yes, no) := by
  simp [stylePartition, ready]

/-- One commit applies the existing pure/mutable/linear policy only to the first
root; preparation of the second root has already succeeded. -/
theorem stylePartition_owner (style : TableStyle) (before yes no : A)
    (prepare : A → Except E (A × A)) (ready : prepare before = .ok (yes, no)) :
    (stylePartition style (some before) prepare).1 =
      (styleStep (E := E) style (some before) (fun _ => .ok yes)).1 := by
  simp [stylePartition, ready]

/-- The second admission is sequenced before ownership installation. -/
def preparePartitionRoots (admit : A → Except E A) (yes no : A) : Except E (A × A) :=
  match admit yes with
  | .error cause => .error cause
  | .ok left => match admit no with
    | .error cause => .error cause
    | .ok right => .ok (left, right)

/-- A late rejection cannot return even the already-admitted first root. -/
theorem preparePartitionRoots_second_refused (admit : A → Except E A) (yes no left : A)
    (cause : E) (first : admit yes = .ok left) (second : admit no = .error cause) :
    preparePartitionRoots admit yes no = .error cause := by
  simp [preparePartitionRoots, first, second]

/-- Pair publication cannot overwrite a reentrant or competing newer generation.
The unused prepared second root remains local on this refusal. -/
theorem installPartition_stale (style : TableStyle) (current : TableGeneration A)
    (expected : Nat) (roots : A × A) (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected roots.1 = (current, .error .stale) :=
  installStyle_stale style current expected roots.1 stale

/-- Ordered splitting reuses two checked selections on the ORIGINAL rows. No
intermediate remainder is required to satisfy a possibly partial root refinement.
The middle observation is an already admitted lookup in that same snapshot. -/
def prepareOrderedSplit (compare : K → Except E Int) (middle : Option V)
    (admit : List (K × V) → Except E Unit) (rows : List (K × V)) :
    Except E (List (K × V) × Option V × List (K × V)) :=
  match selectBindings (fun row => (compare row.1).map (fun sign => decide (sign < 0))) rows with
  | .error cause => .error cause
  | .ok (left, _) => match admit left with
    | .error cause => .error cause
    | .ok () =>
      match selectBindings (fun row => (compare row.1).map (fun sign => decide (sign > 0))) rows with
      | .error cause => .error cause
      | .ok (right, _) => match admit right with
        | .error cause => .error cause
        | .ok () => .ok (left, middle, right)

/-- Under total comparison and admission, both sides are exact stable filters.
This preserves opaque Function payloads without equality or normalization. -/
theorem prepareOrderedSplit_total (compare : K → Int) (middle : Option V)
    (rows : List (K × V)) :
    prepareOrderedSplit (E := E) (fun k => .ok (compare k)) middle (fun _ => .ok ()) rows =
      .ok (rows.filter (fun row => decide (compare row.1 < 0)), middle,
        rows.filter (fun row => decide (compare row.1 > 0))) := by
  simp [prepareOrderedSplit, selectBindings_total, Except.map]

/-- Every original binding belongs to exactly its sign region; the zero region
corresponds to the pivot only under the caller's lawful comparer/key-identity law. -/
theorem orderedSplit_regions (compare : K → Int) (row : K × V) (rows : List (K × V)) :
    row ∈ rows.filter (fun r => decide (compare r.1 < 0)) ∨
      row ∈ rows.filter (fun r => decide (compare r.1 = 0)) ∨
      row ∈ rows.filter (fun r => decide (compare r.1 > 0)) ↔ row ∈ rows := by
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h; rcases h with h | h | h <;> exact h.1
  · intro h
    by_cases less : compare row.1 < 0
    · exact .inl ⟨h, less⟩
    · by_cases same : compare row.1 = 0
      · exact .inr (.inl ⟨h, same⟩)
      · exact .inr (.inr ⟨h, by omega⟩)

/-- Preparing two owners and a non-owning observation uses the same partition
installer. A failure cannot expose the pivot or either prepared capability. -/
def styleSplit (style : TableStyle) (state : Option A)
    (prepare : A → Except E (A × B × A)) :
    Option A × Except (StyleFailure E) (A × B × A) :=
  match state with
  | none => (none, .error .consumed)
  | some before => match prepare before with
    | .error cause => (state, .error (.callback cause))
    | .ok (left, middle, right) =>
      let staged := stylePartition (E := E) style state (fun _ => .ok (left, right))
      (staged.1, .ok (left, middle, right))

/-- Both roots and the exact pivot observation are independent of presentation. -/
theorem styleSplit_observation (style : TableStyle) (before left right : A) (middle : B)
    (prepare : A → Except E (A × B × A)) (ready : prepare before = .ok (left, middle, right)) :
    (styleSplit style (some before) prepare).2 = .ok (left, middle, right) := by
  simp [styleSplit, ready]

/-- Any refusal, including the final root's recognition, preserves the old owner. -/
theorem styleSplit_refused (style : TableStyle) (before : A)
    (prepare : A → Except E (A × B × A)) (cause : E)
    (refused : prepare before = .error cause) :
    styleSplit style (some before) prepare = (some before, .error (.callback cause)) := by
  simp [styleSplit, refused]

/-- Successful linear decomposition retires the predecessor once, even if empty. -/
theorem styleSplit_linear (before left right : A) (middle : B)
    (prepare : A → Except E (A × B × A)) (ready : prepare before = .ok (left, middle, right)) :
    styleSplit .linear (some before) prepare = (none, .ok (left, middle, right)) := by
  simp [styleSplit, ready, stylePartition, styleStep]

/-- A consumed predecessor cannot execute preparation or revive any result. -/
theorem styleSplit_consumed (style : TableStyle) (prepare : A → Except E (A × B × A)) :
    styleSplit style none prepare = (none, .error .consumed) := rfl

/-- No binding can occur on both sides of a lawful sign comparison. -/
theorem orderedSplit_disjoint (compare : K → Int) (row : K × V) (rows : List (K × V)) :
    ¬ (row ∈ rows.filter (fun r => decide (compare r.1 < 0)) ∧
      row ∈ rows.filter (fun r => decide (compare r.1 > 0))) := by
  simp only [List.mem_filter, decide_eq_true_eq]
  intro ⟨⟨_, less⟩, ⟨_, greater⟩⟩
  omega

/-- A late right-root refusal suppresses even the admitted left root and pivot. -/
theorem prepareOrderedSplit_right_refused (compare : K → Int) (middle : Option V)
    (rows : List (K × V)) (admit : List (K × V) → Except E Unit) (cause : E)
    (left : admit (rows.filter (fun row => decide (compare row.1 < 0))) = .ok ())
    (right : admit (rows.filter (fun row => decide (compare row.1 > 0))) = .error cause) :
    prepareOrderedSplit (fun k => .ok (compare k)) middle admit rows = .error cause := by
  simp [prepareOrderedSplit, selectBindings_total, Except.map, left, right]

/-- A left-root refusal stops preparation before the second comparison traversal,
matching the checked map's admission order; neither a pivot nor a side escapes. -/
theorem prepareOrderedSplit_left_refused (compare : K → Except E Int) (middle : Option V)
    (admit : List (K × V) → Except E Unit) (rows left remainder : List (K × V))
    (cause : E)
    (selected : selectBindings (fun row => (compare row.1).map (fun sign => decide (sign < 0)))
      rows = .ok (left, remainder)) (refused : admit left = .error cause) :
    prepareOrderedSplit compare middle admit rows = .error cause := by
  simp [prepareOrderedSplit, selected, refused]

end LeanPoo.Functional.OrderedDictionary
