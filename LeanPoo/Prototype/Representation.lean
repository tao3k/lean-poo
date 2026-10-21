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
  | tree (entries : List (String × Value))
  deriving DecidableEq

/-- Both physical choices must expose precisely the same ordered contributions. -/
def Storage.entries : Storage Value → List (String × Value)
  | .small entries | .tree entries => entries

/-- Count contributions, including duplicates, rather than only unique field names. -/
def pack (entries : List (String × Value)) : Storage Value :=
  if entries.length ≤ 8 then .small entries else .tree entries

/-- Promotion/demotion retain the entire ordered method chain, without evaluation. -/
@[simp] theorem entries_pack (entries : List (String × Value)) : (pack entries).entries = entries := by
  simp only [pack]; split <;> rfl

/-- Exactly the compact branch has the declared bounded contribution count. -/
theorem pack_small_iff (entries : List (String × Value)) :
    pack entries = .small entries ↔ entries.length ≤ 8 := by
  simp only [pack]; split <;> simp_all

/-- Persistent writes use the existing first-contribution operation before repacking. -/
def Storage.put (source : Storage Value) (name : String) (value : Value) : Storage Value :=
  pack (putFirst source.entries name value)

/-- Persistent removal uses the existing all-contribution erasure before repacking. -/
def Storage.remove (source : Storage Value) (name : String) : Storage Value :=
  pack (erase source.entries name)

/-- Either representation preserves all untouched and later same-name contributions. -/
@[simp] theorem entries_put (source : Storage Value) (name : String) (value : Value) :
    (source.put name value).entries = putFirst source.entries name value := by
  simp [Storage.put]

/-- Demotion cannot retain a forgotten direct method or change surviving order. -/
@[simp] theorem entries_remove (source : Storage Value) (name : String) :
    (source.remove name).entries = erase source.entries name := by
  simp [Storage.remove]

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

/-- Shape sharing alone never authorizes reuse across receivers. -/
theorem reject_owner (site : Site) (view : View Value) (different : site.owner ≠ view.owner) :
    read site view = none := by simp [read,valid,different]

/-- An old reference is rejected even if a revision restores the same values/shape. -/
theorem reject_revision (site : Site) (view : View Value) (different : site.revision ≠ view.revision) :
    read site view = none := by simp [read,valid,different]

/-- Replacing a layout rejects old offsets even if the owner and field set coincide. -/
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

end LeanPoo.Prototype.Representation
