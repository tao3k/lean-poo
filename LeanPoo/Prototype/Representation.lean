import LeanPoo.Object.CacheInvalidation

/-! Persistent ordered specifications and guarded receiver-local vector layouts.
This models source semantics, not the standard RBTree implementation, weak-table
collector, Scheme compiler or pointer layout. A runtime layout token denotes one
immutable shape and one receiver's cells; supported edits discard that token.
Registered finite dependency edges and serialized edits remain prerequisites. -/
namespace LeanPoo.Prototype.Representation

/-- Ordered contributions can repeat a name; replacing the first preserves later methods. -/
def putFirst (entries : List (String × Value)) (name : String) (value : Value) : List (String × Value) :=
  match entries with
  | [] => [(name,value)]
  | (key,old) :: tail => if key = name then (key,value) :: tail else (key,old) :: putFirst tail name value

/-- Direct removal erases all local contributions; inheritance is resolved separately. -/
def erase (entries : List (String × Value)) (name : String) := entries.filter (fun entry => entry.1 != name)

/-- Observe the first contribution while retaining the complete ordered method chain. -/
def first (entries : List (String × Value)) (name : String) : Option Value :=
  match entries with
  | [] => none
  | (key,value) :: tail => if key = name then some value else first tail name

/-- Persistent writes replace the intended contribution, including previously absent keys. -/
theorem first_put (entries : List (String × Value)) (name : String) (value : Value) :
    first (putFirst entries name value) name = some value := by
  induction entries with
  | nil => simp [putFirst,first]
  | cons entry tail ih => rcases entry with ⟨key,old⟩; by_cases h : key = name <;> simp [putFirst,first,h,ih]

/-- An unrelated field is unchanged by a persistent write. -/
theorem first_put_frame (entries : List (String × Value)) (name other : String) (value : Value)
    (different : other ≠ name) : first (putFirst entries name value) other = first entries other := by
  induction entries with
  | nil => simp [putFirst,first,Ne.symm different]
  | cons entry tail ih =>
    rcases entry with ⟨key,old⟩
    by_cases h : key = name
    · subst key; simp [putFirst,first,Ne.symm different]
    · simp [putFirst,first,h,ih]

/-- Removing a local name leaves no forgotten same-name contribution. -/
theorem first_erase (entries : List (String × Value)) (name : String) : first (erase entries name) name = none := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key,value⟩
    by_cases h : key = name <;> simp [erase,first,h] at * <;> assumption

/-- A source-level storage refinement. Tree contents denote the standard library's
ordered contribution observation; this does not model balancing or physical cells. -/
inductive Storage (Value : Type) where
  | small (entries : List (String × Value))
  | tree (entries : List (String × Value)) (compact : Bool)
  deriving DecidableEq

/-- Both physical choices must expose precisely the same ordered contributions. -/
def Storage.entries : Storage Value → List (String × Value)
  | .small entries => entries
  | .tree entries _ => entries

/-- Count contributions, including duplicates, rather than only unique field names. -/
def pack (entries : List (String × Value)) : Storage Value :=
  if entries.length ≤ 8 then .small entries else .tree entries true

/-- Promotion/demotion retain the entire ordered method chain, without evaluation. -/
@[simp] theorem entries_pack (entries : List (String × Value)) : (pack entries).entries = entries := by
  simp only [pack]; split <;> rfl

/-- Exactly the compact branch has the declared bounded contribution count. -/
theorem pack_small_iff (entries : List (String × Value)) :
    pack entries = .small entries ↔ entries.length ≤ 8 := by
  simp only [pack]; split <;> simp_all

/-- The explicit policy survives promotion; tree-only mode never enables small maps. -/
def Storage.compact : Storage Value → Bool
  | .small _ => true
  | .tree _ compact => compact

/-- New snapshots default to the standard tree policy; compact storage is explicit. -/
def packWith (compact : Bool) (entries : List (String × Value)) : Storage Value :=
  if compact then pack entries else .tree entries false

/-- Policy selection changes storage, never the ordered contribution observation. -/
@[simp] theorem entries_packWith (compact : Bool) (entries : List (String × Value)) :
    (packWith compact entries).entries = entries := by
  cases compact with
  | false => rfl
  | true => exact entries_pack entries

/-- Representation conversion retains the caller-selected strategy, including large maps. -/
@[simp] theorem compact_packWith (compact : Bool) (entries : List (String × Value)) :
    (packWith compact entries).compact = compact := by
  cases compact <;> by_cases small : entries.length ≤ 8 <;>
    simp [packWith, pack, small, Storage.compact]

/-- Persistent writes use the existing first-contribution operation before repacking. -/
def Storage.put (source : Storage Value) (name : String) (value : Value) : Storage Value :=
  packWith source.compact (putFirst source.entries name value)

/-- Persistent removal uses the existing all-contribution erasure before repacking. -/
def Storage.remove (source : Storage Value) (name : String) : Storage Value :=
  packWith source.compact (erase source.entries name)

/-- Either representation preserves all untouched and later same-name contributions. -/
@[simp] theorem entries_put (source : Storage Value) (name : String) (value : Value) :
    (source.put name value).entries = putFirst source.entries name value := by
  simp [Storage.put]

/-- Demotion cannot retain a forgotten direct method or change surviving order. -/
@[simp] theorem entries_remove (source : Storage Value) (name : String) :
    (source.remove name).entries = erase source.entries name := by
  simp [Storage.remove]

/-- Writes cannot silently enable a rejected automatic policy. -/
@[simp] theorem put_policy (source : Storage Value) (name : String) (value : Value) :
    (source.put name value).compact = source.compact := by simp [Storage.put]

/-- Removal/demotion retains the chosen policy for future revisions. -/
@[simp] theorem remove_policy (source : Storage Value) (name : String) :
    (source.remove name).compact = source.compact := by simp [Storage.remove]

/-- The default tree policy remains a tree even for small or empty revised rows. -/
theorem default_put_tree (entries : List (String × Value)) (name : String) (value : Value) :
    (Storage.tree entries false).put name value = .tree (putFirst entries name value) false := by rfl

/-- The existing first-write law applies across both representation transitions. -/
theorem storage_first_put (source : Storage Value) (name : String) (value : Value) :
    first (source.put name value).entries name = some value := by
  simpa using first_put source.entries name value

/-- A persistent revision cannot change an unrelated field's first contribution. -/
theorem storage_put_frame (source : Storage Value) (name other : String) (value : Value)
    (different : other ≠ name) :
    first (source.put name value).entries other = first source.entries other := by
  simpa using first_put_frame source.entries name other value different

/-- Count actual identity tests in the compact first-name search, including misses. -/
def searchWork (entries : List (String × Value)) (name : String) : Nat :=
  match entries with
  | [] => 0
  | (key, _) :: tail => if key = name then 1 else 1 + searchWork tail name

/-- Compact search never examines more contributions than the stored vector holds. -/
theorem searchWork_le (entries : List (String × Value)) (name : String) :
    searchWork entries name ≤ entries.length := by
  induction entries with
  | nil => simp [searchWork]
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    simp only [searchWork, List.length_cons]
    split <;> omega

/-- A selected compact representation has at most eight identity tests per lookup.
This counts source operations only, not allocator, GC, compiler or wall time. -/
theorem compact_search_bound (entries : List (String × Value)) (name : String)
    (compact : pack entries = .small entries) : searchWork entries name ≤ 8 := by
  exact Nat.le_trans (searchWork_le entries name) ((pack_small_iff entries).mp compact)

/-- First replacement preserves length; a new contribution increases it by one. -/
theorem putFirst_length_le (entries : List (String × Value)) (name : String) (value : Value) :
    (putFirst entries name value).length ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [putFirst]
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    simp only [putFirst, List.length_cons]
    split <;> simp_all only [List.length_cons] <;> omega

/-- Compact writes copy at most nine vector cells, including the promotion row.
Tree construction after promotion has a separate standard-library cost. -/
theorem compact_copy_bound (entries : List (String × Value)) (name : String) (value : Value)
    (compact : pack entries = .small entries) : (putFirst entries name value).length ≤ 9 := by
  have size := (pack_small_iff entries).mp compact
  have written := putFirst_length_le entries name value
  omega

/-- Whole finite revision traces use one semantic operation family in both stores. -/
inductive Edit (Value : Type) where
  | put (name : String) (value : Value)
  | remove (name : String)

/-- One standard semantic revision step on the ordered contribution list. -/
def editEntries (entries : List (String × Value)) : Edit Value → List (String × Value)
  | .put name value => putFirst entries name value
  | .remove name => erase entries name

/-- One revision step through the concrete representation selector. -/
def editStorage (source : Storage Value) : Edit Value → Storage Value
  | .put name value => source.put name value
  | .remove name => source.remove name

/-- Arbitrarily many promotions/demotions preserve the full ordered specification. -/
theorem revision_trace (edits : List (Edit Value)) (source : Storage Value) :
    (edits.foldl editStorage source).entries = edits.foldl editEntries source.entries := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases edit <;> simp [editStorage, editEntries]

/-- A complete finite revision trace preserves the explicitly selected strategy. -/
theorem revision_trace_policy (edits : List (Edit Value)) (source : Storage Value) :
    (edits.foldl editStorage source).compact = source.compact := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases edit <;> simp [editStorage]

/-- A layout has one receiver identity, monotone revision and allocation token.
Shapes may be shared, while the field interpretation belongs to this receiver. -/
structure View (Value : Type) where
  owner : Nat
  revision : Nat
  token : Nat
  names : List String
  fields : String → Option Value

/-- Materialize the receiver's lazy/cached interpretation at its shape index.
An absent cell remains distinct from a present false Boolean. -/
def cell (view : View Value) (index : Nat) : Option Value := view.names[index]?.bind view.fields

/-- An access site retains a certified shape index, never a retained result value. -/
structure Site where
  owner : Nat
  revision : Nat
  token : Nat
  names : List String
  name : String
  index : Nat
  indexed : names[index]? = some name

/-- Runtime identity guards mean the same receiver, revision and immutable layout.
Structural shape equality states the semantic obligation of token/pointer identity. -/
abbrev valid (site : Site) (view : View Value) : Prop :=
  site.owner = view.owner ∧ site.revision = view.revision ∧ site.token = view.token ∧ site.names = view.names

/-- A failed guard publishes no cached value; ordinary lookup performs the miss. -/
def read (site : Site) (view : View Value) : Option Value :=
  if valid site view then cell view site.index else none

/-- Every accepted index observes this receiver's current field, not a different owner. -/
theorem read_sound (site : Site) (view : View Value) (current : valid site view) :
    read site view = view.fields site.name := by
  have indexed : view.names[site.index]? = some site.name := current.2.2.2 ▸ site.indexed
  simp [read,current,cell,indexed]

/-- Shape sharing alone never authorizes the old receiver value guard. -/
theorem reject_owner (site : Site) (view : View Value) (different : site.owner ≠ view.owner) :
    read site view = none := by simp [read,valid,different]

/-- An old reference is rejected even if a revision restores the same values/shape. -/
theorem reject_revision (site : Site) (view : View Value) (different : site.revision ≠ view.revision) :
    read site view = none := by simp [read,valid,different]

/-- Replacing a layout rejects the old value guard, even for equal field sets.
The separate shape-offset path must read the new receiver-local cells. -/
theorem reject_layout (site : Site) (view : View Value) (different : site.token ≠ view.token) :
    read site view = none := by simp [read,valid,different]

/-- Reuse the existing graph theorem: a shared descendant advances exactly once.
This connects the index guard to supported parent/hook/descriptor invalidation. -/
theorem descendant_revision_rejected (graph : C4.Graph) (changed : List String)
    (cache : String → Object.RevisionCache Value) (name : String)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    (cache name).revision ≠ (Object.invalidateCaches graph changed cache name).revision := by
  rw [Object.invalidateCaches_once graph changed cache name affected]
  omega

/-- Present false is a valid vector result and cannot be confused with absence. -/
theorem false_cell (view : View Bool) (index : Nat) (name : String)
    (indexed : view.names[index]? = some name) (present : view.fields name = some false) :
    cell view index = some false := by simp [cell,indexed,present]

/-- Equal immutable shapes certify an offset across receivers, never an old
receiver's value. Runtime pointer equality must imply this shape equality. -/
def reuseIndex (site : Site) (view : View Value) : Option Nat :=
  if site.names = view.names then some site.index else none

/-- A reused offset always denotes the requested name in the CURRENT layout. -/
theorem reuseIndex_sound (site : Site) (view : View Value)
    (same : site.names = view.names) : view.names[site.index]? = some site.name :=
  same ▸ site.indexed

/-- The switched-owner ready-cell path reads this view; an unknown shape or
uncomputed cell uses the existing lazy fallback. No Value equality is required. -/
def readPrepared (site : Site) (view : View Value) (fallback : Unit → Except E Value) : Except E Value :=
  match (reuseIndex site view).bind (cell view) with
  | some value => .ok value
  | none => fallback ()

/-- Owner/revision/token can differ: only the current view supplies the value. -/
theorem readPrepared_current (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (value : Value) (same : site.names = view.names) (ready : view.fields site.name = some value) :
    readPrepared site view fallback = .ok value := by
  have indexed := reuseIndex_sound site view same
  simp [readPrepared, reuseIndex, same, cell, indexed, ready]

/-- A known offset does not force an uncomputed body until its ordinary fallback. -/
theorem readPrepared_lazy (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (same : site.names = view.names) (uncomputed : view.fields site.name = none) :
    readPrepared site view fallback = fallback () := by
  have indexed := reuseIndex_sound site view same
  simp [readPrepared, reuseIndex, same, cell, indexed, uncomputed]

/-- A different shape grants no reusable offset or cached value authority. -/
theorem readPrepared_reshaped (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (different : site.names ≠ view.names) : readPrepared site view fallback = fallback () := by
  simp [readPrepared, reuseIndex, different]

/-- Lazy refusal retains its exact cause; the caller cannot bind a successful value. -/
theorem readPrepared_refused (site : Site) (view : View Value) (cause : E)
    (same : site.names = view.names) (uncomputed : view.fields site.name = none) :
    readPrepared site view (fun _ => .error cause) = .error cause :=
  readPrepared_lazy site view _ same uncomputed

/-- Stored false is ready data, not an uncomputed cell or a request to retry. -/
theorem readPrepared_false (site : Site) (view : View Bool) (fallback : Unit → Except E Bool)
    (same : site.names = view.names) (ready : view.fields site.name = some false) :
    readPrepared site view fallback = .ok false :=
  readPrepared_current site view fallback false same ready

/-- Count only name-to-index hash resolutions in the switched-site path. Shape
checks, value reads, guards, initialization, callback/evaluator and GC costs are
separate; faithful constant-time shape identity is a runtime premise. -/
def resolutionWork (site : Site) (view : View Value) : Nat :=
  if site.names = view.names then 0 else 1

/-- A matching shape removes the name-map resolution, not all access costs. -/
theorem resolutionWork_shared (site : Site) (view : View Value) (same : site.names = view.names) :
    resolutionWork site view = 0 := by simp [resolutionWork, same]

/-- Shape mismatch retains one ordinary resolution rather than inventing an offset. -/
theorem resolutionWork_changed (site : Site) (view : View Value) (different : site.names ≠ view.names) :
    resolutionWork site view = 1 := by simp [resolutionWork, different]

end LeanPoo.Prototype.Representation
