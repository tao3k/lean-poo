import LeanPoo.Functional.ContainerValidation

/-! Existing Pair/Map/Sum/Union validation interpreted with finite pure callbacks.
Map entries are one host-table snapshot; key equivalence must agree with the host
hash policy. Sum tags and ordered Union choices are explicit, without inference. -/
namespace LeanPoo.Functional.VariantValidation

/-- Validate both Pair positions before constructing the normalized pair. -/
def pair (left : A → Except Error A) (right : B → Except Error B) (source : A × B) : Except Error (A × B) :=
  (left source.1).bind fun first => (right source.2).map (first, ·)

/-- Each successful Pair component is the result of its own validator. -/
theorem pair_success (left : A → Except Error A) (right : B → Except Error B) (source checked : A × B) :
    pair left right source = .ok checked ↔ left source.1 = .ok checked.1 ∧ right source.2 = .ok checked.2 := by
  rcases checked with ⟨first, second⟩
  cases hl : left source.1 <;> cases hr : right source.2 <;>
    simp [pair, hl, hr, Except.bind, Except.map]

/-- Left failure preserves its original cause and suppresses right validation. -/
theorem pair_left_error (left : A → Except Error A) (right : B → Except Error B) (source : A × B) (error : Error)
    (failed : left source.1 = .error error) : pair left right source = .error error := by
  simp [pair, failed, Except.bind]

/-- Check normalized keys against the table-supplied equivalence. No canonical
hash iteration order or built-in equality for arbitrary function keys is assumed. -/
def distinctKeys (same : Key → Key → Bool) : List (Key × Value) → Bool
  | [] => true
  | entry :: rest => !(rest.any (fun other => same entry.1 other.1)) && distinctKeys same rest

/-- A successful key check excludes every collision with the head entry. The host
adapter must supply the same equality as its actual table insertion operation. -/
theorem distinctKeys_head (same : Key → Key → Bool) (entry : Key × Value) (rest : List (Key × Value))
    (good : distinctKeys same (entry :: rest) = true) :
    (rest.any (fun other => same entry.1 other.1)) = false ∧ distinctKeys same rest = true := by
  simpa [distinctKeys] using good

/-- Normalize a complete map snapshot, then refuse collisions before installation.
Only a successful complete list can be handed to a representation adapter. -/
def map (key : Key → Except Error Key) (value : Value → Except Error Value)
    (same : Key → Key → Bool) (collision : Error) (entries : List (Key × Value)) : Except Error (List (Key × Value)) :=
  (Validation.traverse (pair key value) entries).bind fun checked =>
    if distinctKeys same checked then .ok checked else .error collision

/-- Successful map normalization preserves all normalized entries and excludes
key collisions. In particular, insertion cannot silently shrink this result. -/
theorem map_success (key : Key → Except Error Key) (value : Value → Except Error Value)
    (same : Key → Key → Bool) (collision : Error) (entries checked : List (Key × Value)) :
    map key value same collision entries = .ok checked ↔
      Validation.traverse (pair key value) entries = .ok checked ∧ distinctKeys same checked = true := by
  cases ht : Validation.traverse (pair key value) entries with
  | error error => simp [map, ht, Except.bind]
  | ok normalized =>
    cases hd : distinctKeys same normalized <;> simp [map, ht, hd, Except.bind]
    all_goals intro equal; subst normalized; simp_all

/-- No entries disappear: length is preserved, and each snapshot position has
exact successful key and value normalizations. Snapshot order is host-supplied. -/
theorem map_positions (key : Key → Except Error Key) (value : Value → Except Error Value)
    (same : Key → Key → Bool) (collision : Error) (entries checked : List (Key × Value))
    (good : map key value same collision entries = .ok checked) :
    checked.length = entries.length ∧ ∀ entry ∈ entries.zip checked,
      key entry.1.1 = .ok entry.2.1 ∧ value entry.1.2 = .ok entry.2.2 := by
  have normalized := (map_success key value same collision entries checked).mp good |>.1
  have positions := ContainerValidation.list_positions (pair key value) entries checked normalized
  exact ⟨positions.1, fun entry member => (pair_success key value entry.1 entry.2).mp (positions.2 entry member)⟩

/-- Original child errors bypass collision/installation and retain their cause. -/
theorem map_child_error (key : Key → Except Error Key) (value : Value → Except Error Value)
    (same : Key → Key → Bool) (collision error : Error) (entries : List (Key × Value))
    (failed : Validation.traverse (pair key value) entries = .error error) :
    map key value same collision entries = .error error := by
  simp [map, failed, Except.bind]

/-- A normalized collision refuses the entire batch before representation commit. -/
theorem map_collision (key : Key → Except Error Key) (value : Value → Except Error Value)
    (same : Key → Key → Bool) (collision : Error) (entries checked : List (Key × Value))
    (normalized : Validation.traverse (pair key value) entries = .ok checked)
    (duplicate : distinctKeys same checked = false) : map key value same collision entries = .error collision := by
  simp [map, normalized, duplicate, Except.bind]

/-- A known Sum tag chooses one payload validator; an unknown tag stops dispatch. -/
def sum (lookup : Tag → Option (Value → Except Error Value)) (missing : Error) (source : Tag × Value) :
    Except Error (Tag × Value) :=
  match lookup source.1 with
  | none => .error missing
  | some check => (check source.2).map (source.1, ·)

/-- Unknown tags cannot apply any payload validator. -/
theorem sum_unknown (lookup : Tag → Option (Value → Except Error Value)) (missing : Error) (source : Tag × Value)
    (unknown : lookup source.1 = none) : sum lookup missing source = .error missing := by
  simp [sum, unknown]

/-- A selected tag remains unchanged while its exact checked payload is installed. -/
theorem sum_selected (lookup : Tag → Option (Value → Except Error Value)) (missing : Error)
    (source : Tag × Value) (check : Value → Except Error Value) (checked : Value)
    (selected : lookup source.1 = some check) (accepted : check source.2 = .ok checked) :
    sum lookup missing source = .ok (source.1, checked) := by
  simp [sum, selected, accepted, Except.map]

/-- Keep a selected payload's original error, without trying another Sum tag. -/
theorem sum_error (lookup : Tag → Option (Value → Except Error Value)) (missing error : Error)
    (source : Tag × Value) (check : Value → Except Error Value)
    (selected : lookup source.1 = some check) (failed : check source.2 = .error error) :
    sum lookup missing source = .error error := by
  simp [sum, selected, failed, Except.map]

/-- Any successful Sum result retains the original tag, independently of payload normalization. -/
theorem sum_tag_preserved (lookup : Tag → Option (Value → Except Error Value)) (missing : Error)
    (source checked : Tag × Value) (good : sum lookup missing source = .ok checked) : checked.1 = source.1 := by
  cases selected : lookup source.1 with
  | none => simp [sum, selected] at good
  | some check =>
    cases normalized : check source.2 with
    | error error => simp [sum, selected, normalized, Except.map] at good
    | ok value =>
      have equal : (source.1, value) = checked := by
        simpa [sum, selected, normalized, Except.map] using good
      exact (congrArg Prod.fst equal).symm

/-- Union selection is ordered structural matching, separate from recognition. -/
def select (shape : Branch → Value → Bool) (branches : List Branch) (source : Value) : Option Branch :=
  branches.find? (fun branch => shape branch source)

/-- Once the head structurally matches, later alternatives cannot replace it. -/
theorem select_head (shape : Branch → Value → Bool) (branch : Branch) (rest : List Branch) (source : Value)
    (matching : shape branch source = true) : select shape (branch :: rest) source = some branch := by
  simp [select, List.find?, matching]

/-- Structural mismatch advances selection before any branch validation starts. -/
theorem select_next (shape : Branch → Value → Bool) (branch : Branch) (rest : List Branch) (source : Value)
    (misses : shape branch source = false) : select shape (branch :: rest) source = select shape rest source := by
  simp [select, List.find?, misses]

/-- Lock one structural branch. Validate its returned value against that branch,
without retrying a later branch after failure or accepting another branch's value. -/
def union (shape member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid : Error) (branches : List Branch) (source : Value) : Except Error Value :=
  match select shape branches source with
  | none => .error missing
  | some branch => (check branch source).bind fun checked =>
      if member branch checked then .ok checked else .error invalid

/-- Empty or structurally unmatched alternatives refuse without validation. -/
theorem union_missing (shape member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid : Error) (branches : List Branch) (source : Value)
    (none : select shape branches source = Option.none) :
    union shape member check missing invalid branches source = .error missing := by
  simp [union, none]

/-- A selected validator error cannot be hidden by a more permissive fallback. -/
theorem union_error (shape member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid error : Error) (branches : List Branch) (source : Value) (branch : Branch)
    (selected : select shape branches source = some branch) (failed : check branch source = .error error) :
    union shape member check missing invalid branches source = .error error := by
  simp [union, selected, failed, Except.bind]

/-- Selection plus successful validation only admits the selected branch's member. -/
theorem union_selected (shape member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid : Error) (branches : List Branch) (source checked : Value) (branch : Branch)
    (selected : select shape branches source = some branch) (normalized : check branch source = .ok checked) :
    union shape member check missing invalid branches source =
      if member branch checked then .ok checked else .error invalid := by
  simp [union, selected, normalized, Except.bind]
/-- Persistent backends first admit and snapshot the carrier, normalize every
binding in order, then rebuild privately. Collision/comparison/postcondition
refusals belong to rebuilding, so earlier backend errors are never reordered. -/
def table (snapshot : Carrier → Except Error (List (Key × Value)))
    (rebuild : List (Key × Value) → Except Error Carrier)
    (key : Key → Except Error Key) (value : Value → Except Error Value)
    (source : Carrier) : Except Error Carrier :=
  (snapshot source).bind fun entries => (Validation.traverse (pair key value) entries).bind rebuild

/-- An accepted backend retains every normalized binding. Key changes can reorder
an ordered tree, so fidelity is permutation rather than an identical snapshot.
Logical normalization order still pairs each source entry with its own wrappers. -/
theorem table_positions (snapshot : Carrier → Except Error (List (Key × Value)))
    (rebuild : List (Key × Value) → Except Error Carrier)
    (key : Key → Except Error Key) (value : Value → Except Error Value) (source result : Carrier)
    (materializes : ∀ entries output, rebuild entries = .ok output →
      ∃ observed, snapshot output = .ok observed ∧ observed.Perm entries)
    (accepted : table snapshot rebuild key value source = .ok result) :
    ∃ before checked observed, snapshot source = .ok before ∧ snapshot result = .ok observed ∧
      observed.Perm checked ∧ observed.length = before.length ∧ ∀ entry ∈ before.zip checked,
        key entry.1.1 = .ok entry.2.1 ∧ value entry.1.2 = .ok entry.2.2 := by
  unfold table at accepted
  cases hs : snapshot source with
  | error error => simp [hs, Except.bind] at accepted
  | ok before =>
    cases ht : Validation.traverse (pair key value) before with
    | error error => simp [hs, ht, Except.bind] at accepted
    | ok checked =>
      have built : rebuild checked = .ok result := by simpa [hs, ht, Except.bind] using accepted
      have positions := ContainerValidation.list_positions (pair key value) before checked ht
      obtain ⟨observed, readBack, reordered⟩ := materializes checked result built
      exact ⟨before, checked, observed, rfl, readBack, reordered,
        reordered.length_eq.trans positions.1,
        fun entry member => (pair_success key value entry.1 entry.2).mp (positions.2 entry member)⟩

/-- Carrier failure stops before normalization and private construction. -/
theorem table_shape_refused (snapshot : Carrier → Except Error (List (Key × Value)))
    (rebuild : List (Key × Value) → Except Error Carrier)
    (key : Key → Except Error Key) (value : Value → Except Error Value)
    (source : Carrier) (error : Error) (failed : snapshot source = .error error) :
    table snapshot rebuild key value source = .error error := by simp [table, failed, Except.bind]

/-- Every original child failure precedes rebuilding and keeps its exact cause.
This is effect sequencing; no rollback of arbitrary user IO is asserted. -/
theorem table_refused (snapshot : Carrier → Except Error (List (Key × Value)))
    (rebuild : List (Key × Value) → Except Error Carrier)
    (key : Key → Except Error Key) (value : Value → Except Error Value)
    (source : Carrier) (before : List (Key × Value)) (error : Error)
    (shape : snapshot source = .ok before)
    (failed : Validation.traverse (pair key value) before = .error error) :
    table snapshot rebuild key value source = .error error := by simp [table, shape, failed, Except.bind]

/-- Collision, insertion and post-recognition errors retain their actual backend
order. A private prefix may exist; it is never a successful returned collection. -/
theorem table_rebuild_refused (snapshot : Carrier → Except Error (List (Key × Value)))
    (rebuild : List (Key × Value) → Except Error Carrier)
    (key : Key → Except Error Key) (value : Value → Except Error Value)
    (source : Carrier) (before entries : List (Key × Value)) (error : Error)
    (shape : snapshot source = .ok before)
    (normalized : Validation.traverse (pair key value) before = .ok entries)
    (refused : rebuild entries = .error error) :
    table snapshot rebuild key value source = .error error := by
  simp [table, shape, normalized, refused, Except.bind]

/-- A consumer never sees a partial candidate after collection refusal. -/
theorem table_consumer_refused (admit : Carrier → Except Error Carrier)
    (consume : Carrier → Except Error Result) (source : Carrier) (error : Error)
    (failed : admit source = .error error) :
    (admit source).bind consume = .error error := by simp [failed, Except.bind]

/-- A persistent revision exposes either a complete checked collection or the
original source; retry runs admission again, without a cached earlier result. -/
def tableRevision (admit : Carrier → Except Error Carrier) (source : Carrier) :
    Except Error Carrier × Carrier :=
  match admit source with
  | .error error => (.error error, source)
  | .ok checked => (.ok checked, checked)

/-- Failure preserves both the error and last source. Host persistent operations
must separately satisfy nonmutation; callback side effects are not rolled back. -/
theorem tableRevision_refused (admit : Carrier → Except Error Carrier) (source : Carrier)
    (error : Error) (failed : admit source = .error error) :
    tableRevision admit source = (.error error, source) := by simp [tableRevision, failed]

/-- A final non-normalizing membership check gates materialization. -/
def tableMaterialize (build : List Entry → Carrier) (member : Carrier → Bool)
    (invalid : Error) (entries : List Entry) : Except Error Carrier :=
  let candidate := build entries
  if member candidate then .ok candidate else .error invalid

/-- Final membership is necessary for every exposed collection. -/
theorem tableMaterialize_sound (build : List Entry → Carrier) (member : Carrier → Bool)
    (invalid : Error) (entries : List Entry) (result : Carrier)
    (accepted : tableMaterialize build member invalid entries = .ok result) : member result = true := by
  dsimp only [tableMaterialize] at accepted
  split at accepted
  · rename_i good
    cases accepted
    exact good
  · simp at accepted

/-- Membership in one closed exact-integer interval. Reversed bounds are empty. -/
def intervalHas (piece : Int × Int) (value : Int) : Prop := piece.1 ≤ value ∧ value ≤ piece.2
/-- Remove one closed cover without sorting or enumerating interval inhabitants. -/
def subtractInterval (source covered : Int × Int) : List (Int × Int) :=
  if covered.2 < covered.1 ∨ source.2 < covered.1 ∨ covered.2 < source.1 then [source]
  else (if source.1 < covered.1 then [(source.1, covered.1 - 1)] else []) ++
       (if covered.2 < source.2 then [(covered.2 + 1, source.2)] else [])
/-- Every uncovered integer survives subtraction in one retained interval. -/
theorem subtractInterval_keeps (source covered : Int × Int) (value : Int)
    (valid : intervalHas source value) (absent : ¬ intervalHas covered value) :
    ∃ piece ∈ subtractInterval source covered, intervalHas piece value := by
  rcases source with ⟨lower, upper⟩
  rcases covered with ⟨left, right⟩
  simp only [intervalHas] at valid absent
  unfold subtractInterval
  split
  · exact ⟨(lower, upper), by simp, valid⟩
  · by_cases before : value < left
    · refine ⟨(lower, left - 1), ?_, ?_⟩
      · simp [show lower < left by omega]
      · simp only [intervalHas]; omega
    · refine ⟨(right + 1, upper), ?_, ?_⟩
      · simp [show right < upper by omega]
      · simp only [intervalHas]; omega
/-- A finite interval family contains an integer when one original piece does. -/
def intervalsContain (pieces : List (Int × Int)) (value : Int) : Prop :=
  ∃ piece ∈ pieces, intervalHas piece value
/-- Ordered subtraction visits each residual through the standard flat-map fold. -/
def uncoveredIntervals : List (Int × Int) → List (Int × Int) → List (Int × Int)
  | [], remaining => remaining
  | covered :: rest, remaining =>
      uncoveredIntervals rest (remaining.flatMap (fun source => subtractInterval source covered))
/-- An integer absent from all covers cannot disappear from the residuals. -/
theorem uncoveredIntervals_keeps (covers remaining : List (Int × Int)) (value : Int)
    (absent : ¬ intervalsContain covers value) (valid : intervalsContain remaining value) :
    intervalsContain (uncoveredIntervals covers remaining) value := by
  induction covers generalizing remaining with
  | nil => exact valid
  | cons covered rest ih =>
    apply ih
    · intro found
      obtain ⟨piece, member, holds⟩ := found
      exact absent ⟨piece, List.mem_cons_of_mem covered member, holds⟩
    · obtain ⟨source, member, holds⟩ := valid
      obtain ⟨piece, retained, holds⟩ := subtractInterval_keeps source covered value holds
        (fun h => absent ⟨covered, by simp, h⟩)
      exact ⟨piece, List.mem_flatMap.mpr ⟨source, member, retained⟩, holds⟩
/-- Coverage is empty residuals, with empty source intervals admitted explicitly. -/
def coversInterval (source : Int × Int) (covers : List (Int × Int)) : Bool :=
  decide (source.2 < source.1) || (uncoveredIntervals covers [source]).isEmpty
/-- Successful finite subtraction covers every integer, independently of width,
branch order, duplicates or overlap. This does not certify host allocation costs. -/
theorem coversInterval_sound (source : Int × Int) (covers : List (Int × Int))
    (accepted : coversInterval source covers = true) (value : Int) (valid : intervalHas source value) :
    intervalsContain covers value := by
  simp only [coversInterval, Bool.or_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with empty | covered
  · simp only [intervalHas] at valid; omega
  · classical
    by_cases present : intervalsContain covers value
    · exact present
    exfalso
    have absent := present
    have retained := uncoveredIntervals_keeps covers [source] value absent ⟨source, by simp, valid⟩
    have empty := List.isEmpty_iff.mp covered
    simp [empty, intervalsContain] at retained
/-- Identity validators preserve the original value through the first selected
flat branch. Recognition coverage never authorizes retry after validation error. -/
theorem union_identity (member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid : Error) (branches : List Branch) (source : Value)
    (accepted : branches.any (fun branch => member branch source) = true)
    (identity : ∀ branch ∈ branches, member branch source = true → check branch source = .ok source) :
    union member member check missing invalid branches source = .ok source := by
  induction branches with
  | nil => simp at accepted
  | cons branch rest ih =>
    cases matching : member branch source
    · have next : rest.any (fun branch => member branch source) = true := by simpa [matching] using accepted
      simpa [union, select, List.find?, matching] using
        ih next (fun b h => identity b (List.mem_cons_of_mem branch h))
    · simp [union, select, List.find?, matching, identity branch (by simp) matching, Except.bind]

/-- Finite mixed scalar sources use ordered membership directly. Identity and
recognizer/shape agreement are explicit premises, not inferred for custom Types. -/
theorem union_finite_identity (member : Branch → Value → Bool) (check : Branch → Value → Except Error Value)
    (missing invalid : Error) (branches : List Branch) (values : List Value)
    (covered : values.all (fun value => branches.any (fun branch => member branch value)) = true)
    (identity : ∀ value ∈ values, ∀ branch ∈ branches,
      member branch value = true → check branch value = .ok value) :
    ∀ value ∈ values, union member member check missing invalid branches value = .ok value := by
  intro value inside
  exact union_identity member check missing invalid branches value
    (List.all_eq_true.mp covered value inside) (identity value inside)

end LeanPoo.Functional.VariantValidation
