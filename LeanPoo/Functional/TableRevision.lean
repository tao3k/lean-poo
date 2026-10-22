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
section Aggregate
variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- Missing contributes zero; stored values, including false, are projected once. -/
def contribution (score : K → V → Int) (key : K) (value : Option V) : Int :=
  (value.map (score key)).getD 0

/-- Full finite reference fold. The inventory is unique and covers every live key. -/
def foldView (inventory : List K) (score : K → V → Int) (view : K → Option V) : Int :=
  inventory.foldr (fun key acc => contribution score key (view key) + acc) 0

/-- Retract the expected old contribution, then add the admitted replacement. -/
def foldStep (score : K → V → Int) (acc : Int) (edit : Change K V) : Int :=
  acc - contribution score edit.key edit.before + contribution score edit.key edit.after

/-- The update performs no inventory scan; only the supplied ordered edits matter. -/
def foldChanges (score : K → V → Int) (edits : List (Change K V)) (acc : Int) : Int :=
  edits.foldl (foldStep score) acc

omit [DecidableEq K] [DecidableEq V] in
/-- The reference fold observes only keys in its supplied finite inventory. -/
theorem foldView_congr (inventory : List K) (score : K → V → Int)
    (left right : K → Option V) (same : ∀ key ∈ inventory, left key = right key) :
    foldView inventory score left = foldView inventory score right := by
  induction inventory with
  | nil => rfl
  | cons key rest ih =>
    simp only [foldView, List.foldr_cons]
    rw [same key (by simp)]
    congr 1
    exact ih (fun k h => same k (by simp [h]))

omit [DecidableEq V] in
/-- The finite reference fold satisfies the optional-write law for exact sums.
Every changed key must be included once; scores may depend on keys and payloads. -/
theorem foldView_replace (inventory : List K) (unique : inventory.Nodup)
    (score : K → V → Int) (view : K → Option V) (key : K) (value : Option V)
    (member : key ∈ inventory) :
    foldView inventory score (replace view key value) =
      foldView inventory score view - contribution score key (view key) + contribution score key value := by
  induction inventory with
  | nil => simp at member
  | cons head rest ih =>
    have tailUnique := (List.nodup_cons.mp unique).2
    by_cases same : key = head
    · subst head
      have apart := (List.nodup_cons.mp unique).1
      have tail : foldView rest score (replace view key value) = foldView rest score view := by
        apply foldView_congr rest score
        intro query inside
        have neq : query ≠ key := by intro eq; subst query; exact apart inside
        simp [replace, neq]
      simp only [foldView, List.foldr_cons, replace, ↓reduceIte]
      change contribution score key value + foldView rest score (replace view key value) = _
      rw [tail]
      simp only [foldView]
      omega
    · have inside : key ∈ rest := by simpa [same] using member
      have different : head ≠ key := Ne.symm same
      have tail := ih tailUnique inside
      simp only [foldView, List.foldr_cons]
      change contribution score head ((replace view key value) head) +
        foldView rest score (replace view key value) = _
      rw [tail]
      simp only [replace, different, ↓reduceIte, foldView]
      omega

/-- Any stable fold with the optional-write law admits sparse updates. This
states the exact premise for user-supplied accumulators, including product metrics;
it does not infer a retractable algebra from the existence of methods. -/
theorem foldl_correct {Acc : Type} (observe : (K → Option V) → Acc)
    (step : Acc → Change K V → Acc) (edits : List (Change K V))
    (write : ∀ view edit, edit ∈ edits →
      observe (replace view edit.key edit.after) =
        step (observe view) ⟨edit.key, view edit.key, edit.after⟩)
    (before after : K → Option V) (success : applyChanges edits before = .ok after) :
    edits.foldl step (observe before) = observe after := by
  induction edits generalizing before with
  | nil => cases success; rfl
  | cons edit rest ih =>
    simp only [applyChanges] at success
    split at success
    next aligned =>
      have head := write before edit (by simp)
      have headEq : step (observe before) edit = observe (replace before edit.key edit.after) := by
        cases edit
        simpa only [aligned] using head.symm
      rw [List.foldl_cons, headEq]
      exact ih (fun view e h => write view e (by simp [h])) _ success
    next => cases success

/-- After successful installation the incremental value equals a complete fold.
Conflict checking itself is still the existing applyChanges operation. -/
theorem foldChanges_correct (inventory : List K) (unique : inventory.Nodup)
    (score : K → V → Int) (edits : List (Change K V))
    (covered : ∀ edit ∈ edits, edit.key ∈ inventory)
    (before after : K → Option V) (success : applyChanges edits before = .ok after) :
    foldChanges score edits (foldView inventory score before) = foldView inventory score after := by
  induction edits generalizing before with
  | nil => cases success; rfl
  | cons edit rest ih =>
    simp only [applyChanges] at success
    split at success
    next aligned =>
      have write := foldView_replace inventory unique score before edit.key edit.after
        (covered edit (by simp))
      simp only [foldChanges, List.foldl_cons]
      change foldChanges score rest (foldStep score (foldView inventory score before) edit) = _
      have head : foldStep score (foldView inventory score before) edit =
          foldView inventory score (replace before edit.key edit.after) := by
        simpa [foldStep, aligned] using write.symm
      rw [head]
      exact ih (fun e h => covered e (by simp [h])) _ success
    next => cases success

/-- Fully check installation before returning either the source or aggregate. -/
def applyFold (score : K → V → Int) (edits : List (Change K V))
    (view : K → Option V) (acc : Int) : Except K ((K → Option V) × Int) :=
  (applyChanges edits view).map fun after => (after, foldChanges score edits acc)

/-- The complete operation returns the full-fold oracle or exactly its old-value
conflict; the error contains no privately staged source or aggregate. -/
theorem applyFold_correct (inventory : List K) (unique : inventory.Nodup)
    (score : K → V → Int) (edits : List (Change K V))
    (covered : ∀ edit ∈ edits, edit.key ∈ inventory) (view : K → Option V) :
    applyFold score edits view (foldView inventory score view) =
      (applyChanges edits view).map (fun after => (after, foldView inventory score after)) := by
  cases success : applyChanges edits view with
  | error key => simp [applyFold, success, Except.map]
  | ok after =>
    have correct := foldChanges_correct inventory unique score edits covered view after success
    simp [applyFold, success, Except.map, correct]

omit [DecidableEq K] [DecidableEq V] in
/-- Undo of exact integer contributions restores any accumulator, independent
of the representation. Full source recovery is applyChanges_inverse. -/
theorem foldChanges_inverse (score : K → V → Int) (edits : List (Change K V)) (acc : Int) :
    foldChanges score (inverseChanges edits) (foldChanges score edits acc) = acc := by
  induction edits generalizing acc with
  | nil => rfl
  | cons edit rest ih =>
    simp only [foldChanges, List.foldl_cons, inverseChanges, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.foldl_append]
    change foldStep score (foldChanges score (inverseChanges rest)
      (foldChanges score rest (foldStep score acc edit))) ⟨edit.key, edit.after, edit.before⟩ = acc
    rw [ih]
    simp only [foldStep]
    omega

/-- Count projection calls, excluding initial scanning, shape checks, lookup,
metadata, arithmetic and allocation. Failure may stop before this upper bound. -/
def foldWork (edits : List (Change K V)) : Nat :=
  edits.foldr (fun edit cost => (if edit.before.isSome then 1 else 0) +
    (if edit.after.isSome then 1 else 0) + cost) 0

omit [DecidableEq K] [DecidableEq V] in
/-- Incremental contribution work is bounded by two projections per edit. -/
theorem foldWork_bound (edits : List (Change K V)) : foldWork edits ≤ 2 * edits.length := by
  induction edits with
  | nil => simp [foldWork]
  | cons edit rest ih =>
    simp only [foldWork, List.foldr_cons, List.length_cons] at *
    split <;> split <;> omega

/-- Pull a contribution function back through the explicit key/value inverses. -/
def transportScore {L W : Type} (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (score : K → V → Int) : L → W → Int :=
  fun key value => score (keys.fromFields key) (values.fromFields value)

omit [DecidableEq K] [DecidableEq V] in
/-- Optional mapped payloads carry exactly the same contribution. -/
theorem transport_contribution {L W : Type} (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (score : K → V → Int)
    (key : K) (value : Option V) :
    contribution (transportScore keys values score) (keys.toFields key)
      (value.map values.toFields) = contribution score key value := by
  cases value <;> simp [contribution, transportScore, keys.from_to, values.from_to]

omit [DecidableEq K] [DecidableEq V] in
/-- Full folds agree under the mapped inventory, without assuming a backend order. -/
theorem transport_foldView {L W : Type} (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (score : K → V → Int)
    (inventory : List K) (view : K → Option V) :
    foldView (inventory.map keys.toFields) (transportScore keys values score)
      (transportView keys values view) = foldView inventory score view := by
  induction inventory with
  | nil => rfl
  | cons key rest ih =>
    simp only [foldView, List.map_cons, List.foldr_cons, transportView, keys.from_to]
    rw [transport_contribution]
    exact congrArg (fun value => contribution score key (view key) + value) ih

omit [DecidableEq K] [DecidableEq V] in
/-- Sparse aggregate updates commute with explicit isomorphism transport. -/
theorem transport_foldChanges {L W : Type} (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (score : K → V → Int)
    (edits : List (Change K V)) (acc : Int) :
    foldChanges (transportScore keys values score) (transportChanges keys values edits) acc =
      foldChanges score edits acc := by
  induction edits generalizing acc with
  | nil => rfl
  | cons edit rest ih =>
    simp only [foldChanges, transportChanges, List.map_cons, List.foldl_cons]
    change foldChanges _ (transportChanges keys values rest)
      (foldStep _ acc (transportChange keys values edit)) = _
    rw [ih]
    simp only [foldStep, transportChange, transport_contribution]
    rfl

/-- The complete source/aggregate result and first refusal key transport together. -/
theorem transport_applyFold {L W : Type} [DecidableEq L] [DecidableEq W]
    (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (score : K → V → Int) (edits : List (Change K V)) (view : K → Option V) (acc : Int) :
    applyFold (transportScore keys values score) (transportChanges keys values edits)
        (transportView keys values view) acc =
      ((applyFold score edits view acc).mapError keys.toFields).map
        (fun result => (transportView keys values result.1, result.2)) := by
  simp only [applyFold]
  rw [transport_applyChanges]
  cases result : applyChanges edits view <;>
    simp [Except.map, Except.mapError, transport_foldChanges]

end Aggregate

section FoldReuse
variable {K V L W : Type} [DecidableEq K] [DecidableEq V]
  [DecidableEq L] [DecidableEq W]

/-- Trusted paired views need only persistent writes after source conflicts pass.
The runtime cache establishes the correspondence before skipping target admission. -/
def writeChanges (edits : List (Change K V)) (view : K → Option V) : K → Option V :=
  edits.foldl (fun current edit => replace current edit.key edit.after) view

/-- Complete source checking establishes the same view as private write-only replay. -/
theorem applyChanges_writeChanges (edits : List (Change K V)) (before after : K → Option V)
    (success : applyChanges edits before = .ok after) : writeChanges edits before = after := by
  induction edits generalizing before with
  | nil => cases success; rfl
  | cons edit rest ih =>
    simp only [applyChanges] at success
    split at success
    · exact ih _ success
    · cases success

omit [DecidableEq V] [DecidableEq W] in
/-- Sparse mapped writes retain the paired-view invariant without a full fold. -/
theorem transport_writeChanges (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (edits : List (Change K V))
    (view : K → Option V) :
    writeChanges (transportChanges keys values edits) (transportView keys values view) =
      transportView keys values (writeChanges edits view) := by
  induction edits generalizing view with
  | nil => rfl
  | cons edit rest ih =>
    simp only [writeChanges, transportChanges, List.map_cons, List.foldl_cons]
    change writeChanges (transportChanges keys values rest)
      (replace (transportView keys values view) (keys.toFields edit.key)
        (edit.after.map values.toFields)) = _
    rw [← transport_replace, ih]
    rfl

/-- Reuse the source aggregate result, updating only the paired target bindings.
The cached target is an explicit input, so correspondence is a visible premise. -/
def reuseFold (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (score : K → V → Int) (edits : List (Change K V))
    (source : K → Option V) (target : L → Option W) (acc : Int) :
    Except L ((L → Option W) × Int) :=
  ((applyFold score edits source acc).mapError keys.toFields).map
    (fun result => (writeChanges (transportChanges keys values edits) target, result.2))

/-- Reusing a lawful aggregate agrees with full target execution, including
its exact first error. No target contribution or full fold is evaluated. -/
theorem reuseFold_correct (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (score : K → V → Int)
    (edits : List (Change K V)) (source : K → Option V) (target : L → Option W)
    (paired : target = transportView keys values source) (acc : Int) :
    reuseFold keys values score edits source target acc =
      applyFold (transportScore keys values score) (transportChanges keys values edits) target acc := by
  subst target
  rw [transport_applyFold]
  unfold reuseFold applyFold
  cases success : applyChanges edits source with
  | error key => rfl
  | ok after =>
    have view := applyChanges_writeChanges edits source after success
    simp only [Except.map, Except.mapError]
    rw [transport_writeChanges, view]

omit [DecidableEq K] [DecidableEq V] [DecidableEq L] [DecidableEq W] in
/-- An independently fresh source with the same observation can rebind an
existing representation. Its aggregate comes from the new admitted source; no
expired source/target certificate or old aggregate is used to infer freshness. -/
theorem rebind_fold_view (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (oldSource freshSource : K → Option V)
    (target : L → Option W) (paired : target = transportView keys values oldSource)
    (same : freshSource = oldSource) (freshAggregate : Int) :
    (target, freshAggregate) = (transportView keys values freshSource, freshAggregate) := by
  rw [same, paired]

omit [DecidableEq K] [DecidableEq V] [DecidableEq L] [DecidableEq W] in
/-- A paired inverse needs neither conversion nor aggregate reconstruction:
its retained source and accumulator are exactly the original ones. -/
theorem retained_fold_inverse (keys : Prototype.DictionaryBridge K L)
    (values : Prototype.DictionaryBridge V W) (source : K → Option V) (acc : Int) :
    (transportView keys.inverse values.inverse (transportView keys values source), acc) =
      (source, acc) := by rw [transportView_inverse]

/-- Metadata reuse is an instance of the existing table frame theorem. Changes
outside one captured scope preserve it, even when another scope is invalidated. -/
theorem fold_dependency_frame {Id : Type} [DecidableEq Id]
    (edits : List (Change Id Nat)) (before after : Id → Option Nat)
    (success : applyChanges edits before = .ok after) (scope : List Id)
    (outside : ∀ edit ∈ edits, edit.key ∉ scope) :
    ∀ key ∈ scope, after key = before key := by
  intro key member
  exact applyChanges_frame edits before after success key (fun edit inside eq =>
    outside edit inside (by simpa [eq] using member))

/-- A changed captured stamp refuses reuse of that scope. Independent scopes
remain governed by fold_dependency_frame, rather than a global cache flush. -/
theorem fold_dependency_changed {Id : Type} [DecidableEq Id]
    (before : Id → Option Nat) (key : Id) (old next : Nat)
    (captured : before key = some old) (different : old ≠ next) :
    replace before key (some next) key ≠ before key := by
  simp only [replace, ↓reduceIte, captured, ne_eq, Option.some.injEq]
  exact Ne.symm different

omit [DecidableEq K] [DecidableEq V] in
/-- Source projections retain their previous bound; target refolding and full
snapshot scans have zero calls on the paired sparse path. This source-work model
excludes shape checks, registry/backend costs, metadata, allocation and GC. -/
def reuseFoldWork (edits : List (Change K V)) : Nat × Nat × Nat := (foldWork edits, 0, 0)

omit [DecidableEq K] [DecidableEq V] in
/-- The paired path keeps the source projection bound and adds no target scans. -/
theorem reuseFoldWork_bound (edits : List (Change K V)) :
    (reuseFoldWork edits).1 ≤ 2 * edits.length ∧
      (reuseFoldWork edits).2.1 = 0 ∧ (reuseFoldWork edits).2.2 = 0 :=
  ⟨foldWork_bound edits, rfl, rfl⟩

end FoldReuse

section MetadataPreparation
variable {Id A : Type}

/-- Finite captured metadata is compared against one stable current snapshot.
This abstracts revision equality, not callback effects or concurrent locking. -/
def stampMatches (scope : List Id) (expected current : Id → Option Nat) : Bool :=
  scope.all (fun key => expected key == current key)

/-- Joint metadata preparation preserves both original dependency scopes. -/
theorem stampMatches_append (left right : List Id) (expected current : Id → Option Nat) :
    stampMatches (left ++ right) expected current =
      (stampMatches left expected current && stampMatches right expected current) := by
  simp [stampMatches, List.all_append]

/-- Deduplicating a shared scope neither drops a dependency nor admits stale stamps. -/
theorem stampMatches_dedup [BEq Id] [LawfulBEq Id] (scope : List Id)
    (expected current : Id → Option Nat) :
    stampMatches scope.eraseDups expected current = stampMatches scope expected current := by
  apply Bool.eq_iff_iff.mpr
  simp [stampMatches, List.all_eq_true]

/-- Preparation retains its value only when the complete captured scope is current.
The refusal is uniform, matching the bridge's stale-metadata boundary. -/
def prepareStamped (scope : List Id) (expected current : Id → Option Nat) (value : A) : Except Unit A :=
  if stampMatches scope expected current then .ok value else .error ()

/-- One deduplicated preparation is equivalent to two nested preparations, on
success and refusal. All reads must belong to the same stable metadata snapshot. -/
theorem prepareStamped_fuse [BEq Id] [LawfulBEq Id] (left right : List Id)
    (expected current : Id → Option Nat) (value : A) :
    (do let _ ← prepareStamped left expected current ()
        prepareStamped right expected current value) =
      prepareStamped (left ++ right).eraseDups expected current value := by
  simp only [prepareStamped, stampMatches_dedup, stampMatches_append]
  cases hl : stampMatches left expected current <;>
    cases hr : stampMatches right expected current <;> rfl

end MetadataPreparation

end LeanPoo.Functional.OrderedDictionary
