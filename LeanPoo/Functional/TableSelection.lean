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

end LeanPoo.Functional.OrderedDictionary
