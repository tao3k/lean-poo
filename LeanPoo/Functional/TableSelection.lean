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


/-- A shared selection boundary admits the original root before any predicate,
then admits both fully prepared results. It never invents an empty seed. -/
def prepareSelection (admit : List A → Except E (List A))
    (classify : A → Except E Bool) (rows : List A) : Except E (List A × List A) :=
  match admit rows with
  | .error cause => .error cause
  | .ok original => match selectBindings classify original with
    | .error cause => .error cause
    | .ok (yes, no) => preparePartitionRoots admit yes no

/-- Original-root refusal suppresses classification even for a structural backend. -/
theorem prepareSelection_input_refused (admit : List A → Except E (List A))
    (classify : A → Except E Bool) (rows : List A) (cause : E)
    (refused : admit rows = .error cause) :
    prepareSelection admit classify rows = .error cause := by
  simp [prepareSelection, refused]

/-- Classifier refusal precedes every output admission and retains its exact cause. -/
theorem prepareSelection_classifier_refused (admit : List A → Except E (List A))
    (classify : A → Except E Bool) (rows : List A) (cause : E)
    (original : admit rows = .ok rows) (refused : selectBindings classify rows = .error cause) :
    prepareSelection admit classify rows = .error cause := by
  simp [prepareSelection, original, refused]

/-- An admitted first branch is still private when the second branch refuses. -/
theorem prepareSelection_second_refused (admit : List A → Except E (List A))
    (classify : A → Except E Bool) (rows yes no : List A) (cause : E)
    (original : admit rows = .ok rows) (selected : selectBindings classify rows = .ok (yes, no))
    (first : admit yes = .ok yes) (second : admit no = .error cause) :
    prepareSelection admit classify rows = .error cause := by
  simp [prepareSelection, original, selected, preparePartitionRoots, first, second]

/-- Both shared boundary and existing owner transaction retain the predecessor
on late refusal. Predicate side effects themselves are outside this state model. -/
theorem styleSelection_second_refused (style : TableStyle)
    (admit : List A → Except E (List A)) (classify : A → Except E Bool)
    (rows yes no : List A) (cause : E)
    (original : admit rows = .ok rows) (selected : selectBindings classify rows = .ok (yes, no))
    (first : admit yes = .ok yes) (second : admit no = .error cause) :
    stylePartition style (some rows) (prepareSelection admit classify) =
      (some rows, .error (.callback cause)) :=
  stylePartition_refused style rows _ cause
    (prepareSelection_second_refused admit classify rows yes no cause original selected first second)

/-- Generic selection stages only persistent deletions. This observation model
needs key equality, never equality or normalization of opaque Function payloads. -/
def eraseSelection [DecidableEq K] (view : K → Option V) (keys : List K) : K → Option V :=
  keys.foldl (fun state key => replace state key none) view

/-- Deletion staging is order/duplicate insensitive at observation level. Exact
backend refusal order remains the supplied fold order rather than this relation. -/
theorem eraseSelection_lookup [DecidableEq K] (view : K → Option V)
    (keys : List K) (query : K) :
    eraseSelection view keys query = if query ∈ keys then none else view query := by
  induction keys generalizing view with
  | nil => rfl
  | cons key rest ih =>
    simp only [eraseSelection, List.foldl_cons] at *
    rw [ih]
    by_cases later : query ∈ rest
    · simp [later]
    · by_cases same : query = key <;> simp [later, same, replace]

/-- On an enumerated binding, deleting the rejected keys is exact stable
selection. Admission is required only for the final root, not a neutral seed. -/
theorem eraseSelection_selected [DecidableEq K] (view : K → Option V)
    (keys : List K) (keep : K → Bool) (query : K) (present : query ∈ keys) :
    eraseSelection view (keys.filter (fun key => !keep key)) query =
      if keep query then view query else none := by
  rw [eraseSelection_lookup]
  cases decision : keep query <;> simp [decision, present]

/-- Untouched leaves, including checked closures, retain the exact old value. -/
theorem eraseSelection_frame [DecidableEq K] (view : K → Option V)
    (keys : List K) (query : K) (outside : query ∉ keys) :
    eraseSelection view keys query = view query := by
  simp [eraseSelection_lookup, outside]

/-- With no removals, the reference path performs no persistent writes at all. -/
theorem eraseSelection_no_writes [DecidableEq K] (view : K → Option V) :
    eraseSelection view [] = view := rfl

/-- Generic partition captures exactly one deletion per original binding across
its two branches. This counts edits, not backend allocation or wall-clock time. -/
theorem selection_deletion_budget (keep : K → Bool) (keys : List K) :
    (keys.filter keep).length + (keys.filter (fun key => !keep key)).length = keys.length := by
  exact selectBindings_length (E := Unit) (fun key => .ok (keep key)) keys _ _
    (selectBindings_total keep keys)

/-- Representation transport preserves both branch order and opaque identities
when the visible classifier agrees. Carrier inverse laws remain separate premises. -/
theorem selectBindings_transport (translate : A → B) (source : A → Except E Bool)
    (target : B → Except E Bool) (aligned : ∀ row, target (translate row) = source row)
    (rows : List A) :
    selectBindings target (rows.map translate) =
      (selectBindings source rows).map (fun roots => (roots.1.map translate, roots.2.map translate)) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    cases hc : source head with
    | error cause => simp [selectBindings, aligned, hc, Except.map]
    | ok chosen =>
      cases ht : selectBindings source tail with
      | error cause => simp [selectBindings, aligned, hc, ih, ht, Except.map]
      | ok roots => cases chosen <;> simp [selectBindings, aligned, hc, ih, ht, Except.map]

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

/-- Default extraction follows the declared finite backend traversal. It neither
compares nor rebuilds an opaque selected payload. -/
def deconsBindings (rows : List A) : Option A × List A :=
  match rows with
  | [] => (none, [])
  | head :: tail => (some head, tail)

/-- Putting the optional observation back in front recovers the entire traversal. -/
theorem deconsBindings_reconstruct (rows : List A) :
    (deconsBindings rows).1.toList ++ (deconsBindings rows).2 = rows := by
  cases rows <;> rfl

/-- Optional absence means an empty source, including when A contains false/Unit. -/
theorem deconsBindings_none (rows : List A) : (deconsBindings rows).1 = none ↔ rows = [] := by
  cases rows <;> simp [deconsBindings]

/-- Every nonempty extraction removes exactly one entry, with multiplicity intact. -/
theorem deconsBindings_length (head : A) (tail : List A) :
    (deconsBindings (head :: tail)).2.length + 1 = (head :: tail).length := by simp [deconsBindings]

/-- One chosen binding becomes an ordinary old-value guarded removal. -/
def deconsChange (row : K × V) : List (Change K V) := [⟨row.1, some row.2, none⟩]

/-- A faithful choice installs precisely the chosen-key removal; no full diff is needed. -/
theorem deconsChange_apply [DecidableEq K] [DecidableEq V]
    (view : K → Option V) (row : K × V) (faithful : view row.1 = some row.2) :
    applyChanges (deconsChange row) view = .ok (replace view row.1 none) := by
  simp [deconsChange, applyChanges, faithful]

/-- A missing or changed selected binding refuses with the original conflict key. -/
theorem deconsChange_conflict [DecidableEq K] [DecidableEq V]
    (view : K → Option V) (row : K × V) (mismatch : view row.1 ≠ some row.2) :
    applyChanges (deconsChange row) view = .error row.1 := by
  simp [deconsChange, applyChanges, mismatch]

/-- Every other key is framed independently of backend ordering or payload equality. -/
theorem deconsChange_frame [DecidableEq K] (view : K → Option V) (row : K × V)
    (query : K) (other : query ≠ row.1) : replace view row.1 none query = view query := by
  simp [replace, other]

/-- The exact inverse delta restores the full source observation after extraction. -/
theorem deconsChange_inverse [DecidableEq K] [DecidableEq V]
    (view : K → Option V) (row : K × V) (faithful : view row.1 = some row.2) :
    applyChanges (inverseChanges (deconsChange row)) (replace view row.1 none) = .ok view :=
  applyChanges_inverse _ _ _ (deconsChange_apply view row faithful)

/-- Source admission, captured choice, guarded removal and whole-remainder
recognition precede the returned observation. Required empty extraction refuses
before any installation; external callback effects are not rolled back. -/
def prepareDecons (admit : S → Except E Unit) (choose : S → Except E (Option B))
    (remove : S → B → Except E S) (missing : E) (required : Bool) (source : S) :
    Except E (Option B × S) :=
  (admit source).bind fun _ => (choose source).bind fun found =>
    match found with
    | none => if required then .error missing else .ok (none, source)
    | some row => (remove source row).bind fun rest => (admit rest).map fun _ => (found, rest)

/-- Invalid sources suppress choice and removal, preserving the exact refusal. -/
theorem prepareDecons_source_refused (admit : S → Except E Unit)
    (choose : S → Except E (Option B)) (remove : S → B → Except E S)
    (missing cause : E) (required : Bool) (source : S) (bad : admit source = .error cause) :
    prepareDecons admit choose remove missing required source = .error cause := by
  simp [prepareDecons, bad, Except.bind]

/-- Optional empty extraction retains the admitted source and exposes no false payload. -/
theorem prepareDecons_empty (admit : S → Except E Unit)
    (choose : S → Except E (Option B)) (remove : S → B → Except E S)
    (missing : E) (source : S) (valid : admit source = .ok ()) (empty : choose source = .ok none) :
    prepareDecons admit choose remove missing false source = .ok (none, source) := by
  simp [prepareDecons, valid, empty, Except.bind]

/-- Required empty extraction has its distinct existing Option cause. -/
theorem prepareDecons_required_empty (admit : S → Except E Unit)
    (choose : S → Except E (Option B)) (remove : S → B → Except E S)
    (missing : E) (source : S) (valid : admit source = .ok ()) (empty : choose source = .ok none) :
    prepareDecons admit choose remove missing true source = .error missing := by
  simp [prepareDecons, valid, empty, Except.bind]

/-- Even a valid chosen binding cannot escape when the whole remainder refuses. -/
theorem prepareDecons_remainder_refused (admit : S → Except E Unit)
    (choose : S → Except E (Option B)) (remove : S → B → Except E S)
    (missing cause : E) (required : Bool) (source rest : S) (row : B)
    (valid : admit source = .ok ()) (chosen : choose source = .ok (some row))
    (removed : remove source row = .ok rest) (bad : admit rest = .error cause) :
    prepareDecons admit choose remove missing required source = .error cause := by
  simp [prepareDecons, valid, chosen, removed, bad, Except.bind, Except.map]

/-- Non-owning extracted data stays private until the same single-root installer
accepts the captured generation. A stale or consumed owner leaks no observation. -/
def installDecons (style : TableStyle) (current : TableGeneration A)
    (expected : Nat) (found : B) (rest : A) :
    TableGeneration A × Except (StyleFailure E) (B × A) :=
  let result := installStyle (E := E) style current expected rest
  (result.1, result.2.map (found, ·))

/-- A competing generation rejects both the prepared remainder and selected data. -/
theorem installDecons_stale (style : TableStyle) (current : TableGeneration A)
    (expected : Nat) (found : B) (rest : A) (stale : current.version ≠ expected) :
    installDecons (E := E) style current expected found rest = (current, .error .stale) := by
  simp [installDecons, installStyle_stale style current expected rest stale, Except.map]

/-- Successful installation preserves the exact observation and existing ownership
policy. Pure/posh, mutable/classy and linear share this single-root result. -/
theorem installDecons_ready (style : TableStyle) (current next : TableGeneration A)
    (expected : Nat) (found : B) (rest : A)
    (ready : installStyle (E := E) style current expected rest = (next, .ok rest)) :
    installDecons (E := E) style current expected found rest = (next, .ok (found, rest)) := by
  simp [installDecons, ready, Except.map]

/-- Finite counter selection follows backend visitation order. It models the
stateful Bool predicate passed to the existing filter, not repeated extraction. -/
def prefixBindings (count : Nat) (keepPrefix : Bool) : List A → List A
  | [] => []
  | row :: rest =>
    if count = 0 then
      if keepPrefix then [] else row :: rest
    else if keepPrefix then row :: prefixBindings (count - 1) keepPrefix rest
      else prefixBindings (count - 1) keepPrefix rest

/-- Taking a prefix retains exactly the first min(count,length) payload identities. -/
theorem prefixBindings_take (count : Nat) (rows : List A) :
    prefixBindings count true rows = rows.take count := by
  induction rows generalizing count with
  | nil => simp [prefixBindings]
  | cons row rest ih =>
    cases count with
    | zero => simp [prefixBindings]
    | succ n => simp [prefixBindings, ih]

/-- Dropping uses the same counter and traversal, with the complementary decision. -/
theorem prefixBindings_drop (count : Nat) (rows : List A) :
    prefixBindings count false rows = rows.drop count := by
  induction rows generalizing count with
  | nil => simp [prefixBindings]
  | cons row rest ih =>
    cases count with
    | zero => simp [prefixBindings]
    | succ n => simp [prefixBindings, ih]

/-- The complementary views reconstruct the exact traversal, without payload equality. -/
theorem prefixBindings_reconstruct (count : Nat) (rows : List A) :
    prefixBindings count true rows ++ prefixBindings count false rows = rows := by
  rw [prefixBindings_take, prefixBindings_drop, List.take_append_drop]

/-- Repeated draining is one cumulative drop on observations, without claiming
that intermediate refined roots are necessarily admitted. -/
theorem prefixBindings_drop_add (first second : Nat) (rows : List A) :
    prefixBindings second false (prefixBindings first false rows) =
      prefixBindings (first + second) false rows := by
  simp only [prefixBindings_drop, List.drop_drop]

/-- Signed host counts are admitted before selection. Only the original and the
complete selected root are recognized; no intermediate remainder is required. -/
def preparePrefix (badCount : E) (admit : List A → Except E Unit)
    (count : Int) (keepPrefix : Bool) (rows : List A) : Except E (List A) :=
  if count < 0 then .error badCount else
    (admit rows).bind fun _ =>
      let selected := prefixBindings count.toNat keepPrefix rows
      (admit selected).map fun _ => selected

/-- Negative counts preserve the supplied cause and suppress root admission. -/
theorem preparePrefix_negative (badCount : E) (admit : List A → Except E Unit)
    (count : Int) (keepPrefix : Bool) (rows : List A) (negative : count < 0) :
    preparePrefix badCount admit count keepPrefix rows = .error badCount := by
  simp [preparePrefix, negative]

/-- Original-root refusal suppresses selection and retains its cause. -/
theorem preparePrefix_source_refused (badCount cause : E) (admit : List A → Except E Unit)
    (count : Nat) (keepPrefix : Bool) (rows : List A) (refused : admit rows = .error cause) :
    preparePrefix badCount admit count keepPrefix rows = .error cause := by
  simp [preparePrefix, Int.not_lt.mpr (Int.natCast_nonneg count), refused, Except.bind]

/-- Final-root refusal is exact and exposes no candidate for publication. -/
theorem preparePrefix_refused (badCount cause : E) (admit : List A → Except E Unit)
    (count : Nat) (keepPrefix : Bool) (rows : List A) (source : admit rows = .ok ())
    (refused : admit (prefixBindings count keepPrefix rows) = .error cause) :
    preparePrefix badCount admit count keepPrefix rows = .error cause := by
  simp [preparePrefix, Int.not_lt.mpr (Int.natCast_nonneg count), source, refused, Except.bind, Except.map]

/-- Successful preparation recognizes only the full result; partial refinements
on intermediate removals cannot cause a spurious refusal. Existing installStyle
then supplies generation/consumption/retry laws without a second ownership engine. -/
theorem preparePrefix_ready (badCount : E) (admit : List A → Except E Unit)
    (count : Nat) (keepPrefix : Bool) (rows : List A) (source : admit rows = .ok ())
    (ready : admit (prefixBindings count keepPrefix rows) = .ok ()) :
    preparePrefix badCount admit count keepPrefix rows = .ok (prefixBindings count keepPrefix rows) := by
  simp [preparePrefix, source, ready, Except.bind, Except.map]

/-- A failed complete prefix leaves every style's predecessor retryable. -/
theorem styleStep_prefix_refused (style : TableStyle) (badCount cause : E)
    (admit : List A → Except E Unit) (count : Nat) (keepPrefix : Bool) (rows : List A)
    (source : admit rows = .ok ())
    (refused : admit (prefixBindings count keepPrefix rows) = .error cause) :
    styleStep style (some rows) (preparePrefix badCount admit count keepPrefix) =
      (some rows, .error (.callback cause)) := by
  have denied := preparePrefix_refused badCount cause admit count keepPrefix rows source refused
  simp [styleStep, denied]

end LeanPoo.Functional.OrderedDictionary
