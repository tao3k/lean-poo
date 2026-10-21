import LeanPoo.Functional.OrderedDictionary
import LeanPoo.Prototype.LensLaws
import LeanPoo.Prototype.DictionaryBridge

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

section Isomorphism
variable {K L V W : Type}
open Prototype (DictionaryBridge)

/-- Explicit value conversion preserves absence and carries admitted payloads unchanged
except for the supplied bijection. Function handles may be opaque payloads. -/
def transportView (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (view : K → Option V) : L → Option W :=
  fun key => (view (keys.fromFields key)).map values.toFields

/-- Translate one edit, retaining both expectations and replacements. -/
def transportChange (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (edit : Change K V) : Change L W :=
  ⟨keys.toFields edit.key, edit.before.map values.toFields, edit.after.map values.toFields⟩

/-- List map preserves edit order, including the first possible conflict. -/
def transportChanges (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (edits : List (Change K V)) : List (Change L W) := edits.map (transportChange keys values)

/-- A lawful explicit key conversion cannot collapse distinct keys. -/
theorem transport_key_injective (keys : DictionaryBridge K L) : Function.Injective keys.toFields := by
  intro a b same
  have recovered := congrArg keys.fromFields same
  simpa only [keys.from_to] using recovered

/-- Optional expectation equality is reflected, not merely preserved. -/
theorem transport_option_injective (values : DictionaryBridge V W) :
    Function.Injective (Option.map values.toFields) := by
  intro a b same
  have recovered := congrArg (Option.map values.fromFields) same
  simpa [Option.map_map, Function.comp_def, values.from_to] using recovered

/-- Both inverse laws restore the complete source observation at every key. -/
theorem transportView_inverse (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (view : K → Option V) :
    transportView keys.inverse values.inverse (transportView keys values view) = view := by
  funext key
  simp [transportView, DictionaryBridge.inverse, keys.from_to, Option.map_map,
    Function.comp_def, values.from_to]

/-- Delta inversion commutes with explicit conversion without reordering edits. -/
theorem transportChanges_inverse (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (edits : List (Change K V)) :
    transportChanges keys.inverse values.inverse (transportChanges keys values edits) = edits := by
  induction edits with
  | nil => rfl
  | cons edit rest ih =>
    cases edit
    simp [transportChanges, transportChange, DictionaryBridge.inverse, keys.from_to,
      Option.map_map, Function.comp_def, values.from_to, transportChanges] at *

/-- Undo reverses order in either representation in exactly the same way. -/
theorem transport_inverseChanges (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (edits : List (Change K V)) :
    transportChanges keys values (inverseChanges edits) =
      inverseChanges (transportChanges keys values edits) := by
  simp [transportChanges, inverseChanges, List.map_reverse, List.map_map,
    Function.comp_def, transportChange]

/-- Persistent optional writes commute with the two explicit bijections. -/
theorem transport_replace [DecidableEq K] [DecidableEq L]
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (view : K → Option V) (key : K) (value : Option V) :
    transportView keys values (replace view key value) =
      replace (transportView keys values view) (keys.toFields key) (value.map values.toFields) := by
  funext query
  have same : keys.fromFields query = key ↔ query = keys.toFields key := by
    constructor
    · intro h
      rw [← keys.to_from query, h]
    · intro h
      rw [h, keys.from_to]
  simp only [transportView, replace]
  by_cases h : query = keys.toFields key
  · simp [h, keys.from_to]
  · simp [same, h]

/-- Discovery uses the transported finite inventory in its original order.
No enumeration of all possible keys, or inferred conversion law, is required. -/
theorem transport_diffChanges [DecidableEq V] [DecidableEq W]
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (inventory : List K) (before after : K → Option V) :
    diffChanges (inventory.map keys.toFields)
        (transportView keys values before) (transportView keys values after) =
      transportChanges keys values (diffChanges inventory before after) := by
  induction inventory with
  | nil => rfl
  | cons key rest ih =>
    have same : (before key).map values.toFields = (after key).map values.toFields ↔
        before key = after key := (transport_option_injective values).eq_iff
    simp only [List.map_cons, diffChanges, List.filterMap_cons, transportView,
      keys.from_to, same]
    by_cases aligned : before key = after key
    · simp only [aligned, ↓reduceIte]
      exact ih
    · simp only [aligned, ↓reduceIte]
      change _ :: _ = _ :: _
      congr 1

/-- Installation commutes on success and on refusal, mapping the exact first
conflict key. Universal inverse laws and carrier admission remain explicit premises. -/
theorem transport_applyChanges [DecidableEq K] [DecidableEq L]
    [DecidableEq V] [DecidableEq W]
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (edits : List (Change K V)) (view : K → Option V) :
    applyChanges (transportChanges keys values edits) (transportView keys values view) =
      ((applyChanges edits view).mapError keys.toFields).map (transportView keys values) := by
  induction edits generalizing view with
  | nil => rfl
  | cons edit rest ih =>
    have same : (view edit.key).map values.toFields = edit.before.map values.toFields ↔
        view edit.key = edit.before := (transport_option_injective values).eq_iff
    simp only [transportChanges, List.map_cons, applyChanges, transportChange,
      transportView, keys.from_to]
    by_cases aligned : view edit.key = edit.before
    · simp only [aligned, ↓reduceIte]
      rw [← transport_replace]
      exact ih _
    · simp only [same, aligned, ↓reduceIte]
      rfl

end Isomorphism
end LeanPoo.Functional.OrderedDictionary
