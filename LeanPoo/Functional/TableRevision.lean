import LeanPoo.Functional.OrderedDictionary
import LeanPoo.Prototype.LensLaws

/-! Finite optimistic table deltas over the existing dictionary observation model.
Carrier laws are explicit premises; this does not verify Gerbil's tree runtime. -/
namespace LeanPoo.Functional.OrderedDictionary

variable {Key Value : Type} [DecidableEq Key] [DecidableEq Value]

/-- Missing and stored false are distinct through Option; edits preserve payloads. -/
structure Change (Key Value : Type) where
  key : Key
  before : Option Value
  after : Option Value
  deriving DecidableEq, Repr

/-- Optional replacement is insertion/overwrite or deletion at one logical key. -/
def replace (view : Key → Option Value) (key : Key) (value : Option Value) : Key → Option Value :=
  fun query => if query = key then value else view query

/-- Compare changed bindings in caller order, exposing no intermediate snapshot
on refusal. Unrelated bindings are deliberately permitted to differ. -/
def applyChanges (changes : List (Change Key Value)) (view : Key → Option Value) :
    Except Key (Key → Option Value) :=
  match changes with
  | [] => .ok view
  | change :: rest =>
    if view change.key = change.before then
      applyChanges rest (replace view change.key change.after)
    else .error change.key

/-- Reverse both the operation order and expected/replacement values. -/
def inverseChanges (changes : List (Change Key Value)) : List (Change Key Value) :=
  changes.reverse.map (fun change => ⟨change.key, change.after, change.before⟩)

/-- Discover changed bindings in a finite supplied key order. The carrier must
supply each key once, covering the union of the two finite domains. -/
def diffChanges (keys : List Key) (before after : Key → Option Value) : List (Change Key Value) :=
  keys.filterMap fun key =>
    if before key = after key then none else some ⟨key, before key, after key⟩

omit [DecidableEq Key] in
/-- Finite discovery depends only on observations at the supplied keys. -/
theorem diffChanges_congr (keys : List Key) (left right target : Key → Option Value)
    (same : ∀ key ∈ keys, left key = right key) :
    diffChanges keys left target = diffChanges keys right target := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [diffChanges, List.filterMap_cons]
    rw [same key (by simp)]
    change _ = _
    have tail := ih (fun k h => same k (by simp [h]))
    simp only [diffChanges] at tail
    rw [tail]

/-- Applying a discovered delta succeeds on its source and performs exactly the
finite target replacements, assuming unique keys from the collection protocol. -/
theorem apply_diffChanges (keys : List Key) (unique : keys.Nodup)
    (before after : Key → Option Value) :
    applyChanges (diffChanges keys before after) before =
      .ok (keys.foldl (fun view key => replace view key (after key)) before) := by
  induction keys generalizing before with
  | nil => rfl
  | cons key rest ih =>
    have tailUnique := (List.nodup_cons.mp unique).2
    have apart := (List.nodup_cons.mp unique).1
    have tailSame : diffChanges rest before after =
        diffChanges rest (replace before key (after key)) after :=
      diffChanges_congr rest _ _ _ (fun query member => by
        have different : query ≠ key := by intro eq; subst query; exact apart member
        simp [replace, different])
    simp only [diffChanges, List.filterMap_cons, List.foldl_cons]
    by_cases same : before key = after key
    · simp only [same, ↓reduceIte]
      have unchanged : replace before key (after key) = before := by
        funext query; by_cases eq : query = key <;> simp_all [replace]
      rw [unchanged]
      exact ih tailUnique before
    · simp only [same, ↓reduceIte]
      change applyChanges (Change.mk key (before key) (after key) :: diffChanges rest before after) before = _
      simp only [applyChanges, ↓reduceIte]
      rw [tailSame]
      exact ih tailUnique _

omit [DecidableEq Value] in
/-- Logical lookup after finite replacement depends only on key membership. -/
theorem replacements_lookup (keys : List Key) (before after : Key → Option Value) (query : Key) :
    (keys.foldl (fun view key => replace view key (after key)) before) query =
      if query ∈ keys then after query else before query := by
  induction keys generalizing before with
  | nil => simp
  | cons key rest ih =>
    rw [List.foldl_cons, ih]
    by_cases member : query ∈ rest <;> by_cases same : query = key <;>
      simp_all [replace]

/-- Discovery plus installation reconstructs the entire target when the finite
key inventory covers every difference. No enumeration of an infinite type occurs. -/
theorem diff_complete (keys : List Key) (unique : keys.Nodup)
    (before after : Key → Option Value)
    (covered : ∀ key, key ∉ keys → before key = after key) :
    applyChanges (diffChanges keys before after) before = .ok after := by
  rw [apply_diffChanges keys unique]
  congr 1
  funext key
  rw [replacements_lookup]
  split
  · rfl
  · exact covered key ‹_›

theorem applyChanges_append (left right : List (Change Key Value)) (view : Key → Option Value) :
    applyChanges (left ++ right) view = (applyChanges left view).bind (applyChanges right) := by
  induction left generalizing view with
  | nil => rfl
  | cons change rest ih =>
    simp only [List.cons_append, applyChanges]
    split
    · exact ih _
    · rfl

/-- Reversing a successful finite sequence restores its complete original view,
including bindings outside the edit domain. This is not merely a roundtrip test. -/
theorem applyChanges_inverse (changes : List (Change Key Value)) (before after : Key → Option Value)
    (success : applyChanges changes before = .ok after) :
    applyChanges (inverseChanges changes) after = .ok before := by
  induction changes generalizing before after with
  | nil => cases success; rfl
  | cons change rest ih =>
    simp only [applyChanges] at success
    split at success
    next aligned =>
      have undo := ih _ _ success
      have restored : replace (replace before change.key change.after) change.key change.before = before := by
        funext key
        by_cases same : key = change.key
        · subst key; simp [replace, aligned]
        · simp [replace, same]
      simp only [inverseChanges, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [applyChanges_append]
      change (applyChanges (inverseChanges rest) after).bind _ = _
      rw [undo]
      change (if (replace before change.key change.after) change.key = change.after then
        Except.ok (replace (replace before change.key change.after) change.key change.before)
        else Except.error change.key) = _
      rw [ite_eq_left (by simp [replace]), restored]
    next => cases success

/-- An untouched binding remains exactly the same abstract payload. -/
theorem applyChanges_frame (changes : List (Change Key Value)) (before after : Key → Option Value)
    (success : applyChanges changes before = .ok after) (key : Key)
    (outside : ∀ change ∈ changes, key ≠ change.key) : after key = before key := by
  induction changes generalizing before with
  | nil => cases success; rfl
  | cons change rest ih =>
    simp only [applyChanges] at success
    split at success
    · rw [ih _ success (fun entry member => outside entry (by simp [member]))]
      exact ite_eq_right (outside change (by simp))
    · cases success

omit [DecidableEq Value] in
/-- The optional table focus has all three lens laws, even at an absent key. -/
theorem optional_lens (key : Key) :
    Prototype.LensLaws (fun view : Key → Option Value => view key)
      (fun value view => replace view key value) := by
  constructor
  · intro view; funext query; by_cases same : query = key <;> simp [replace, same]
  · intro view value; simp [replace]
  · intro view first second; funext query; simp [replace]; split <;> rfl

/-- A representation supplies persistent optional writes and their lookup law.
No assumption about physical shape, balancing, allocation or GC is hidden here. -/
structure TableCarrier (Key Value Carrier : Type) [DecidableEq Key] where
  read : Carrier → Key → Option Value
  write : Carrier → Key → Option Value → Carrier
  read_write : ∀ source key value, read (write source key value) = replace (read source) key value

/-- Execute only the finite changed keys on the selected existing backend. -/
def TableCarrier.apply (ops : TableCarrier Key Value Carrier)
    (changes : List (Change Key Value)) (source : Carrier) : Except Key Carrier :=
  match changes with
  | [] => .ok source
  | change :: rest =>
    if ops.read source change.key = change.before then
      ops.apply rest (ops.write source change.key change.after)
    else .error change.key

/-- Every conforming persistent backend implements the same delta semantics,
including the first conflict key. Thus equal views permit cross-carrier reuse. -/
theorem TableCarrier.apply_read (ops : TableCarrier Key Value Carrier)
    (changes : List (Change Key Value)) (source : Carrier) :
    (ops.apply changes source).map ops.read = applyChanges changes (ops.read source) := by
  induction changes generalizing source with
  | nil => rfl
  | cons change rest ih =>
    simp only [TableCarrier.apply, applyChanges]
    split
    · rw [ih, ops.read_write]
    · rfl

/-- Carrier transport preserves all success observations and the exact error.
Full representation isomorphism is stronger than needed: lookup agreement suffices. -/
theorem transport_changes (left : TableCarrier Key Value A) (right : TableCarrier Key Value B)
    (changes : List (Change Key Value)) (a : A) (b : B) (same : left.read a = right.read b) :
    (left.apply changes a).map left.read = (right.apply changes b).map right.read := by
  rw [left.apply_read, right.apply_read, same]

/-- Immediate disagreement refuses before any later edits can be observed. -/
theorem reject_changed (change : Change Key Value) (rest : List (Change Key Value))
    (view : Key → Option Value) (stale : view change.key ≠ change.before) :
    applyChanges (change :: rest) view = .error change.key := by simp [applyChanges, stale]

end LeanPoo.Functional.OrderedDictionary
