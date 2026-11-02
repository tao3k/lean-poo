import LeanPoo.Functional.StrongComponents

/-! Immutable batches precede whole SCC reconstruction and joint admission.
Future-work laws require accepted finite graph certificates and declared reads. -/
namespace LeanPoo.Functional.GeneralizedGraph
universe u
variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

/-- Dependent writes preserve each key's exact value type, including explicit absence. -/
def selectEdit {Cell : Key → Type u} : List (Sigma Cell) → (key : Key) → Option (Cell key)
  | [], _ => none
  | entry :: rest, key => if same : entry.1 = key then some (same ▸ entry.2) else selectEdit rest key

/-- A missing edit retains the old value rather than being confused with absence. -/
theorem selectEdit_none {Cell : Key → Type u} (edits : List (Sigma Cell)) (key : Key)
    (missing : key ∉ edits.map Sigma.fst) : selectEdit edits key = none := by
  induction edits with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp [selectEdit, Ne.symm missing.1, ih missing.2]

/-- A unique selected write is installed with its actual dependent payload. -/
theorem selectEdit_at {Cell : Key → Type u} (edits : List (Sigma Cell)) (key : Key) (value : Cell key)
    (unique : (edits.map Sigma.fst).Nodup) (member : Sigma.mk key value ∈ edits) :
    selectEdit edits key = some value := by
  induction edits with
  | nil => simp at member
  | cons entry rest ih =>
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst entry; simp [selectEdit]
    · have different : entry.1 ≠ key := by
        have nodup := List.nodup_cons.mp unique
        intro same
        apply nodup.1
        rw [same]
        exact List.mem_map.mpr ⟨⟨key,value⟩,member,rfl⟩
      simp [selectEdit, different, ih (List.nodup_cons.mp unique).2 member]

/-- An admitted batch can change a key's code and base together, but duplicate
writes within either namespace and unsupported targets are rejected. -/
structure Revision (spec : Declaration Key Value) where
  codes : List ((key : Key) × Option (Code Key Value key))
  bases : List ((key : Key) × Option (Outcome Key Value key))
  uniqueCodes : (codes.map Sigma.fst).Nodup
  uniqueBases : (bases.map Sigma.fst).Nodup
  knownCodes : ∀ key ∈ codes.map Sigma.fst, key ∈ spec.keys
  knownBases : ∀ key ∈ bases.map Sigma.fst, key ∈ spec.keys

/-- Validate the whole edit batch before any constructor or admission callback. -/
def Revision.create (spec : Declaration Key Value)
    (codes : List ((key : Key) × Option (Code Key Value key)))
    (bases : List ((key : Key) × Option (Outcome Key Value key))) : Except String (Revision spec) :=
  if valid : (codes.map Sigma.fst).Nodup ∧ (bases.map Sigma.fst).Nodup ∧
      (∀ key ∈ codes.map Sigma.fst, key ∈ spec.keys) ∧ (∀ key ∈ bases.map Sigma.fst, key ∈ spec.keys) then
    .ok ⟨codes,bases,valid.1,valid.2.1,valid.2.2.1,valid.2.2.2⟩
  else .error "duplicate or unsupported component revision"

/-- A successful admission preserves the exact submitted edit lists. -/
theorem Revision.create_fields (spec : Declaration Key Value)
    (codes : List ((key : Key) × Option (Code Key Value key)))
    (bases : List ((key : Key) × Option (Outcome Key Value key))) (revision : Revision spec)
    (accepted : Revision.create spec codes bases = .ok revision) :
    revision.codes = codes ∧ revision.bases = bases := by
  unfold create at accepted
  split at accepted
  · cases accepted; exact ⟨rfl,rfl⟩
  · contradiction

/-- Install both namespaces on one immutable final source; no partial source is published. -/
def Revision.apply {spec : Declaration Key Value} (revision : Revision spec) : Declaration Key Value :=
  { spec with
    code := fun key => (selectEdit revision.codes key).getD (spec.code key)
    base := fun key => (selectEdit revision.bases key).getD (spec.base key) }

/-- SCC regrouping keeps finite node support; group support may still merge/split. -/
theorem Revision.apply_keys {spec : Declaration Key Value} (revision : Revision spec) :
    revision.apply.keys = spec.keys := rfl

/-- All staged method bodies appear together in the source used for reconstruction. -/
theorem Revision.apply_code_at {spec : Declaration Key Value} (revision : Revision spec)
    (key : Key) (code : Option (Code Key Value key)) (member : ⟨key,code⟩ ∈ revision.codes) :
    revision.apply.code key = code := by
  simp [apply, selectEdit_at revision.codes key code revision.uniqueCodes member]

/-- Explicit missing input is an actual staged absence, not a skipped base edit. -/
theorem Revision.apply_base_at {spec : Declaration Key Value} (revision : Revision spec)
    (key : Key) (value : Option (Outcome Key Value key)) (member : ⟨key,value⟩ ∈ revision.bases) :
    revision.apply.base key = value := by
  simp [apply, selectEdit_at revision.bases key value revision.uniqueBases member]

/-- Unedited components retain the exact resolver across a multi-service batch. -/
theorem Revision.apply_resolve_frame {spec : Declaration Key Value} (revision : Revision spec)
    (key : Key) (noCode : key ∉ revision.codes.map Sigma.fst) (noBase : key ∉ revision.bases.map Sigma.fst)
    (self : State Key Value) : revision.apply.resolve key self = spec.resolve key self := by
  simp [Declaration.resolve, apply, selectEdit_none revision.codes key noCode,
    selectEdit_none revision.bases key noBase]
end LeanPoo.Functional.GeneralizedGraph

namespace LeanPoo.Functional.StrongComponents
/-- Independent revision reasons combine by union, with no lost dirty reader. -/
theorem Checked.dirty_union {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (left right : Fin n → Bool) (key : Fin n) :
    graph.dirty (fun node => left node || right node) key =
      (graph.dirty left key || graph.dirty right key) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Checked.dirty, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨node, member, path, reason⟩
    rcases reason with dirty | dirty
    · exact Or.inl ⟨node,member,path,dirty⟩
    · exact Or.inr ⟨node,member,path,dirty⟩
  · rintro (⟨node, member, path, dirty⟩ | ⟨node, member, path, dirty⟩)
    · exact ⟨node,member,path,Or.inl dirty⟩
    · exact ⟨node,member,path,Or.inr dirty⟩

/-- After migration, an obsolete source can be edited without dirtying detached
services when no NEW graph path reaches a seed. Resolver equality is still needed
for actual cache reuse; this proves the graph-side condition only. -/
theorem Checked.clean_if_no_seed {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (seed : Fin n → Bool) (key : Fin n)
    (safe : ∀ node, Reach edge key node → seed node = false) : graph.dirty seed key = false := by
  cases result : graph.dirty seed key with
  | false => rfl
  | true =>
    obtain ⟨node,_,changed⟩ := List.any_eq_true.mp result
    have both : graph.rel key node = true ∧ seed node = true := by
      simpa only [Bool.and_eq_true] using changed
    have clean := safe node (graph.sound key node both.1)
    simp [clean] at both

/-- Migrating a shared member invalidates unchanged consumers that reach it in
its NEW group, even when representative names or projected values stay equal. -/
theorem migration_reader_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Checked oldEdge) (next : Checked newEdge) (body : Fin n → Bool) (shared reader : Fin n)
    (moved : old.members shared ≠ next.members shared) (reads : Reach newEdge reader shared) :
    next.dirty (revisionSeed old next body) reader = true :=
  next.reader_dirty _ reader shared ((next.exact reader shared).mpr reads)
    (membership_change_dirty old next body shared moved)

/-- Any number of changed groups may participate in one accepted revision; each
new-graph reader of ANY changed member is dirty. There is no one-group assumption. -/
theorem simultaneous_revision_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Checked oldEdge) (next : Checked newEdge) (body : Fin n → Bool)
    (changed : List (Fin n)) (changes : ∀ node ∈ changed, old.members node ≠ next.members node)
    (reader : Fin n) (affected : ∃ node ∈ changed, Reach newEdge reader node) :
    next.dirty (revisionSeed old next body) reader = true := by
  obtain ⟨node,member,reads⟩ := affected
  exact migration_reader_dirty old next body node reader (changes node member) reads
end LeanPoo.Functional.StrongComponents
