import LeanPoo.Prototype.Representation

/-! Sparse ordered indices, private traversal and persistent composition frames.
The standard RBTree supplies persistent keyed operations; this finite model proves
the name/ordinal contract, not balancing, pointer sharing or machine-time bounds.
Ordinals identify contributions, while String keys identify symbols injectively.
-/
namespace LeanPoo.Prototype.Representation

/-- Record another contribution while retaining the FIRST replacement ordinal. -/
def rememberPosition (positions : List Nat) (next : Nat) : List Nat :=
  match positions with
  | [] => [next]
  | first :: rest => first :: next :: rest

/-- Every new position is recorded, and no earlier method position disappears. -/
theorem rememberPosition_mem (positions : List Nat) (next index : Nat) :
    index ∈ rememberPosition positions next ↔ index = next ∨ index ∈ positions := by
  cases positions with
  | nil => simp [rememberPosition]
  | cons first rest => simp [rememberPosition, or_left_comm]

/-- Duplicate declarations keep first-method replacement independent of tail order. -/
@[simp] theorem rememberPosition_first (first next : Nat) (rest : List Nat) :
    (rememberPosition (first :: rest) next).head? = some first := rfl

/-- Logical position count grows by one; a singleton needs no physical list. -/
@[simp] theorem rememberPosition_length (positions : List Nat) (next : Nat) :
    (rememberPosition positions next).length = positions.length + 1 := by
  cases positions <;> simp [rememberPosition] <;> omega

/-- Unordered duplicate tails contain exactly the same ordinals as ordered append. -/
theorem rememberPosition_perm (positions : List Nat) (next : Nat) :
    (rememberPosition positions next).Perm (positions ++ [next]) := by
  cases positions with
  | nil => simp [rememberPosition]
  | cons first rest =>
    have swap : ([next] ++ rest).Perm (rest ++ [next]) := List.perm_append_comm
    exact swap.cons first

/-- Observe payloads in contribution order; gaps in private ordinals are invisible. -/
def orderedPayloads (entries : List (Nat × (String × Value))) := entries.map Prod.snd

/-- The private name index must contain exactly the ordinals of this name. -/
def IndexMatches (entries : List (Nat × (String × Value))) (name : String)
    (positions : List Nat) : Prop :=
  ∀ entry ∈ entries, entry.1 ∈ positions ↔ entry.2.1 = name

/-- Semantic effect of delegating every indexed ordinal to persistent removal. -/
def erasePositions (entries : List (Nat × (String × Value))) (positions : List Nat) :=
  entries.filter (fun entry => !positions.contains entry.1)

/-- Complete indexed removal has the same observation as the old full filter. -/
theorem erasePositions_observe (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (indexed : IndexMatches entries name positions) :
    orderedPayloads (erasePositions entries positions) = erase (orderedPayloads entries) name := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    have head := indexed entry (by simp)
    have rest : IndexMatches tail name positions := fun item present => indexed item (by simp [present])
    have step := ih rest
    by_cases same : entry.2.1 = name
    · have present := head.mpr same
      simp [erasePositions, orderedPayloads, erase, present, same] at step ⊢
      exact step
    · have absent : entry.1 ∉ positions := fun present => same (head.mp present)
      simp [erasePositions, orderedPayloads, erase, absent, same] at step ⊢
      exact step

/-- A successful removal forgets every same-name method, not only the first. -/
theorem erasePositions_absent (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (indexed : IndexMatches entries name positions) :
    first (orderedPayloads (erasePositions entries positions)) name = none := by
  rw [erasePositions_observe entries name positions indexed]
  exact first_erase _ name

/-- Indexed deletion refines the existing storage/edit protocol for either policy. -/
theorem erasePositions_storage (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (compact : Bool)
    (indexed : IndexMatches entries name positions) :
    orderedPayloads (erasePositions entries positions) =
      (editStorage (packWith compact (orderedPayloads entries)) (.remove name)).entries := by
  rw [erasePositions_observe entries name positions indexed]
  simp [editStorage]

/-- Any untouched name's ordinal index remains valid without reconstruction. -/
theorem erasePositions_preserves_index (entries : List (Nat × (String × Value)))
    (positions other : List Nat) (name : String) (indexed : IndexMatches entries name other) :
    IndexMatches (erasePositions entries positions) name other := by
  intro entry present
  exact indexed entry (List.mem_filter.mp present).1

/-- No positions means no persistent tree work and the exact original observation. -/
@[simp] theorem erasePositions_empty (entries : List (Nat × (String × Value))) :
    erasePositions entries [] = entries := by simp [erasePositions]

/-- New contributions use a high-water ordinal, never the number of live entries. -/
def appendPosition (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) := entries ++ [(next, (name, value))]

/-- Appending after arbitrary gaps retains every surviving contribution in order. -/
@[simp] theorem appendPosition_observe (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) :
    orderedPayloads (appendPosition entries next name value) = orderedPayloads entries ++ [(name, value)] := by
  simp [appendPosition, orderedPayloads]

/-- The next ordinal strictly exceeds every live position. -/
def PositionsBelow (entries : List (Nat × (String × Value))) (next : Nat) : Prop :=
  ∀ entry ∈ entries, entry.1 < next

/-- Deletion retains the high-water certificate even when live count shrinks. -/
theorem positionsBelow_erase (entries : List (Nat × (String × Value)))
    (next : Nat) (positions : List Nat) (bound : PositionsBelow entries next) :
    PositionsBelow (erasePositions entries positions) next := by
  intro entry present
  exact bound entry (List.mem_filter.mp present).1

/-- Advancing the high-water mark makes repeated delete/reinsert append safe. -/
theorem positionsBelow_append (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) (bound : PositionsBelow entries next) :
    PositionsBelow (appendPosition entries next name value) (next + 1) := by
  intro entry present
  simp only [appendPosition, List.mem_append, List.mem_singleton] at present
  rcases present with old | rfl
  · exact Nat.lt_trans (bound entry old) (by omega)
  · simp

/-- Fresh insertion cannot replace an unrelated survivor with the same ordinal. -/
theorem next_position_fresh (entries : List (Nat × (String × Value)))
    (next : Nat) (bound : PositionsBelow entries next) (entry) (present : entry ∈ entries) :
    entry.1 ≠ next := Nat.ne_of_lt (bound entry present)

/-- The canonical finite index used to state admission and primitive-work counts. -/
def matchingPositions (entries : List (Nat × (String × Value))) (name : String) :=
  (entries.filter (fun entry => entry.2.1 == name)).map Prod.fst

/-- Key uniqueness makes a derived index sound even after ordinal gaps appear. -/
theorem matchingPositions_valid (entries : List (Nat × (String × Value)))
    (name : String)
    (unique : ∀ a ∈ entries, ∀ b ∈ entries, a.1 = b.1 → a.2.1 = b.2.1) :
    IndexMatches entries name (matchingPositions entries name) := by
  intro entry present
  constructor
  · intro indexed
    obtain ⟨other, selected, equal⟩ := List.mem_map.mp indexed
    obtain ⟨old, chosen⟩ := List.mem_filter.mp selected
    have same : other.2.1 = name := by simpa using chosen
    exact (unique entry present other old equal.symm).trans same
  · intro same
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨present, by simp [same]⟩, rfl⟩

/-- Present-name work: one lookup, one deletion per contribution and one index removal.
The standard tree's per-operation cost and bounded compact demotion are separate. -/
def indexedEraseWork (positions : List Nat) := positions.length + 2

/-- Sparse deletion's delegated work depends on matching methods, not unrelated names. -/
theorem indexedEraseWork_exact (entries : List (Nat × (String × Value))) (name : String) :
    indexedEraseWork (matchingPositions entries name) =
      (entries.filter (fun entry => entry.2.1 == name)).length + 2 := by
  simp [indexedEraseWork, matchingPositions]

/-- Cost needs an exact index certificate: semantic membership alone can admit
unused ordinals. Permutation permits the implementation's unordered duplicate tail. -/
theorem indexedEraseWork_permutation (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat)
    (complete : positions.Perm (matchingPositions entries name)) :
    indexedEraseWork positions =
      (entries.filter (fun entry => entry.2.1 == name)).length + 2 := by
  rw [indexedEraseWork, complete.length_eq]
  simp [matchingPositions]

/-- Public snapshots own pairs/spines while sharing each immutable key/payload identity. -/
def entrySnapshot (entries : List (String × Value)) := entries.map (fun entry => (entry.1, entry.2))

/-- Copying representation containers does not change their ordered observations. -/
theorem entrySnapshot_value (entries : List (String × Value)) : entrySnapshot entries = entries := by
  simp [entrySnapshot]

/-- Ordered callbacks may update abstract state or refuse with an arbitrary cause.
E can itself carry partial effects; no effect rollback is asserted. -/
def visitEntries (consume : State → String → Value → Except E State)
    (entries : List (String × Value)) (state : State) : Except E State :=
  match entries with
  | [] => .ok state
  | (name,value) :: tail => match consume state name value with
    | .error cause => .error cause
    | .ok next => visitEntries consume tail next

/-- Traversing the private ordered root agrees with the original public-snapshot
composition for ALL callbacks, including false/Function payloads and refusals. -/
theorem visitEntries_snapshot (consume : State → String → Value → Except E State)
    (entries : List (String × Value)) (state : State) :
    visitEntries consume (entrySnapshot entries) state = visitEntries consume entries state := by
  rw [entrySnapshot_value]

/-- Callback order composes exactly across declaration/direct-map boundaries. -/
theorem visitEntries_append (consume : State → String → Value → Except E State)
    (before after : List (String × Value)) (state : State) :
    visitEntries consume (before ++ after) state =
      (visitEntries consume before state).bind (visitEntries consume after) := by
  induction before generalizing state with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨name,value⟩
    simp only [List.cons_append, visitEntries]
    cases consume state name value with
    | error cause => rfl
    | ok next => exact ih next

/-- The first refusal propagates its exact cause without visiting the suffix. -/
theorem visitEntries_refused (consume : State → String → Value → Except E State)
    (name : String) (value : Value) (tail : List (String × Value)) (state : State)
    (cause : E) (refused : consume state name value = .error cause) :
    visitEntries consume ((name,value) :: tail) state = .error cause := by
  simp [visitEntries, refused]

/-- Name-only projection preserves order and duplicates without snapshot pairs. -/
def entryKeys (entries : List (String × Value)) := entries.map Prod.fst

/-- The specialized projection equals map-car over the owned public snapshot. -/
theorem entryKeys_snapshot (entries : List (String × Value)) :
    (entrySnapshot entries).map Prod.fst = entryKeys entries := by
  rw [entrySnapshot_value]; rfl

/-- Composition shares immutable direct maps and starts a fresh logical cache.
Parent linearization, descriptor admission and real storage sharing remain host
premises; this models no raw mutable aliasing or RBTree implementation. -/
def composeMetadata (slots defaults : Storage Value) :
    Storage Value × Storage Value × Object.RevisionCache Value :=
  (slots, defaults, ⟨0, none⟩)

/-- Composition preserves both ordered contribution streams and explicit policies. -/
theorem composeMetadata_frame (slots defaults : Storage Value) :
    (composeMetadata slots defaults).1.entries = slots.entries ∧
    (composeMetadata slots defaults).2.1.entries = defaults.entries ∧
    (composeMetadata slots defaults).1.compact = slots.compact ∧
    (composeMetadata slots defaults).2.1.compact = defaults.compact := ⟨rfl,rfl,rfl,rfl⟩

/-- Shared specifications never authorize sharing an already computed value. -/
theorem composeMetadata_cold (slots defaults : Storage Value) :
    (composeMetadata slots defaults).2.2.derived = none ∧
    (composeMetadata slots defaults).2.2.revision = 0 := ⟨rfl,rfl⟩

/-- A persistent successor does not mutate the direct maps retained by composition. -/
theorem composeMetadata_persistent (slots defaults : Storage Value) (name : String) (value : Value) :
    ((composeMetadata slots defaults).1.entries, (slots.put name value).entries) =
      (slots.entries, putFirst slots.entries name value) := by simp [composeMetadata]

/-- Logical exported cons cells only; iterator stacks, callbacks, hash probes,
construction, retained trees and GC are additional costs. -/
def snapshotExportCells (entries : Nat) := 2 * entries

/-- Direct traversal exports no pairs/spine; names export only one owned spine. -/
theorem keysExportCells_saving (entries : Nat) :
    entries + snapshotExportCells entries = 3 * entries := by
  simp [snapshotExportCells]; omega

/-- Sharing source maps avoids export cells, not fresh receiver/parent preparation. -/
def compositionExportCells (slots defaults : Nat) (shared : Bool) :=
  if shared then 0 else snapshotExportCells slots + snapshotExportCells defaults

/-- Rebuilding via public observations pays both complete export streams. -/
theorem compositionExportCells_saving (slots defaults : Nat) :
    compositionExportCells slots defaults false - compositionExportCells slots defaults true =
      2 * (slots + defaults) := by simp [compositionExportCells, snapshotExportCells, Nat.mul_add]

/-- An owned public catalog observation and its authoritative immutable root.
The host must capture input pairs and keep standard persistent storage private;
this model does not prove physical non-aliasing in the Scheme collector. -/
structure CatalogView (Value : Type) where
  root : Storage Value
  publicEntries : List (String × Value)

/-- Export the same descriptors in order; payloads are shared, never evaluated. -/
def exposeCatalog (root : Storage Value) : CatalogView Value :=
  ⟨root, entrySnapshot root.entries⟩

/-- A client can replace its public list without an edit to the registered source. -/
def CatalogView.replacePublic (view : CatalogView Value)
    (entries : List (String × Value)) : CatalogView Value := { view with publicEntries := entries }

/-- Public-list edits leave membership, payloads, policy and layout names intact. -/
theorem catalog_public_frame (root : Storage Value) (client : List (String × Value)) :
    ((exposeCatalog root).replacePublic client).root = root ∧
    entryKeys ((exposeCatalog root).replacePublic client).root.entries = entryKeys root.entries :=
  ⟨rfl, rfl⟩

/-- Exact snapshot observations include false and function payloads without equality tests. -/
theorem catalog_snapshot (root : Storage Value) :
    (exposeCatalog root).publicEntries = root.entries := entrySnapshot_value _

/-- Constructor grammar admission precedes storage capture. The finite Symbol
pair/list recognizer is a host premise; descriptor elaboration stays lazy. -/
def captureCatalog (compact : Bool) (admitted : Except E (List (String × Value))) :
    Except E (Storage Value) := admitted.map (packWith compact)

/-- Grammar refusal preserves the original cause, without constructing a catalog. -/
theorem captureCatalog_refused (compact : Bool) (cause : E) :
    captureCatalog compact (.error cause : Except E (List (String × Value))) = .error cause := rfl

/-- Successful capture preserves the complete ordered stream, including duplicates. -/
theorem captureCatalog_entries (compact : Bool) (entries : List (String × Value)) :
    (captureCatalog compact (.ok entries) : Except E (Storage Value)).map Storage.entries = .ok entries := by
  simp [captureCatalog, Except.map, entries_packWith]

/-- Elaborate current descriptors into private scratch state before publication.
Callbacks must obey the host registered-source protocol; exceptions return no
partially published state. This is not a rollback of arbitrary external effects. -/
def prepareCatalog (root : Storage Value) (initial : State)
    (consume : State → String → Value → Except E State) : Except E (Storage Value × State) :=
  (visitEntries consume root.entries initial).map (fun state => (root, state))

/-- A descriptor refusal publishes neither scratch metadata nor a replacement root. -/
theorem prepareCatalog_refused (root : Storage Value) (initial : State)
    (consume : State → String → Value → Except E State) (cause : E)
    (refused : visitEntries consume root.entries initial = .error cause) :
    prepareCatalog root initial consume = .error cause := by
  simp [prepareCatalog, refused, Except.map]

/-- A corrected retry starts from fresh scratch and retains the authoritative root. -/
theorem prepareCatalog_retry (root : Storage Value) (initial result : State)
    (consume : State → String → Value → Except E State)
    (accepted : visitEntries consume root.entries initial = .ok result) :
    prepareCatalog root initial consume = .ok (root, result) := by
  simp [prepareCatalog, accepted, Except.map]

/-- Canonical empty roots retain explicit policy without shared mutable builders. -/
theorem catalog_empty_policies :
    (packWith false ([] : List (String × Value))).entries = [] ∧
    (packWith true ([] : List (String × Value))).entries = [] := by simp

/-- Catalog-root reuse avoids public export cells only. Initial grammar admission,
descriptor/tree construction, fresh receivers, registration, hooks and GC are
additional charged costs; physical sharing and machine time remain runtime facts. -/
def catalogExportCells (entries : Nat) (shared : Bool) := if shared then 0 else snapshotExportCells entries

/-- Reuse removes exactly the public spine/pair export from the recapture strategy. -/
theorem catalogExportCells_saving (entries : Nat) :
    catalogExportCells entries false - catalogExportCells entries true = 2 * entries := by
  simp [catalogExportCells, snapshotExportCells]

/-- Compose existing finite grammar capture and lazy descriptor preparation.
The host's standard proper-list recognizer rejects foreign, improper and cyclic
carriers BEFORE this finite model or any elaboration callback is entered. -/
def captureThenPrepareCatalog (compact : Bool) (admitted : Except E (List (String × Value)))
    (initial : State) (consume : State → String → Value → Except E State) :
    Except E (Storage Value × State) :=
  match captureCatalog compact admitted with
  | .error cause => .error cause
  | .ok root => prepareCatalog root initial consume

/-- An input grammar refusal cannot invoke the supplied descriptor continuation. -/
theorem captureThenPrepareCatalog_refused (compact : Bool) (cause : E) (initial : State)
    (consume : State → String → Value → Except E State) :
    captureThenPrepareCatalog compact (.error cause) initial consume = .error cause := rfl

/-- Storage policy cannot change admitted observations, callback order or failure.
This does not extend the input language to arbitrary Iterables or prove the host
list recognizer, callback termination, physical allocation or machine-time bounds. -/
theorem captureThenPrepareCatalog_policy (admitted : Except E (List (String × Value)))
    (initial : State) (consume : State → String → Value → Except E State) :
    (captureThenPrepareCatalog true admitted initial consume).map
      (fun result => (result.1.entries, result.2)) =
    (captureThenPrepareCatalog false admitted initial consume).map
      (fun result => (result.1.entries, result.2)) := by
  cases admitted with
  | error cause => rfl
  | ok entries =>
    simp only [captureThenPrepareCatalog, captureCatalog, Except.map, prepareCatalog,
      entries_packWith]
    cases visitEntries consume entries initial <;> simp [entries_packWith]

/-- A corrected finite request can retry without weakening grammar admission. -/
theorem captureThenPrepareCatalog_retry (compact : Bool) (entries : List (String × Value))
    (initial result : State) (consume : State → String → Value → Except E State)
    (ready : visitEntries consume entries initial = .ok result) :
    captureThenPrepareCatalog compact (.ok entries) initial consume =
      .ok (packWith compact entries, result) := by
  simp [captureThenPrepareCatalog, captureCatalog, prepareCatalog, Except.map, entries_packWith, ready]

/-- The existing publication boundary retains the caller's whole source/cache
state on grammar refusal; no revision or credential can be invalidated by it. -/
theorem captureThenPrepareCatalog_refused_frame (compact : Bool) (cause : String)
    (old : State) (consume : State → String → Value → Except String State) :
    Object.publishEdit old
      ((captureThenPrepareCatalog compact (.error cause) old consume).map Prod.snd) = old := rfl

end LeanPoo.Prototype.Representation
