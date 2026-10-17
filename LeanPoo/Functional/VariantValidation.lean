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
end LeanPoo.Functional.VariantValidation
