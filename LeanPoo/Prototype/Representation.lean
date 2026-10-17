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
