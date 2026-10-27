import LeanPoo.Functional.TableStyle

/-! Correlated index views over one persistent primary. Finite uniqueness
validation is a reference oracle; the warm implementation uses existing indexes
and changed keys rather than this oracle's quadratic enumeration. -/
namespace LeanPoo.Functional.OrderedDictionary

variable {K V I N A : Type} [DecidableEq K] [DecidableEq I]

/-- A grouped index observes the exact original row at its declared projection. -/
def indexView (project : K → V → I) (primary : K → Option V) (bucket : I) (key : K) : Option V :=
  match primary key with
  | none => none
  | some row => if project key row = bucket then some row else none

/-- Retraction removes every touched primary column before any new insertion. -/
def retractIndex (keys : List K) (cache : I → K → Option V) : I → K → Option V :=
  fun bucket key => if key ∈ keys then none else cache bucket key

/-- Final insertion restores only touched columns from the final admitted primary. -/
def insertIndex (keys : List K) (project : K → V → I) (primary : K → Option V)
    (cache : I → K → Option V) : I → K → Option V :=
  fun bucket key => if key ∈ keys then indexView project primary bucket key else cache bucket key

/-- Two phases permit identifier swaps and ignore transient uniqueness violations. -/
def reviseIndex (keys : List K) (project : K → V → I) (after : K → Option V)
    (cache : I → K → Option V) : I → K → Option V :=
  insertIndex keys project after (retractIndex keys cache)

/-- The two-phase algorithm depends on membership, not key-list uniqueness/order. -/
theorem reviseIndex_lookup (keys : List K) (project : K → V → I) (after : K → Option V)
    (cache : I → K → Option V) (bucket : I) (key : K) :
    reviseIndex keys project after cache bucket key =
      if key ∈ keys then indexView project after bucket key else cache bucket key := by
  by_cases h : key ∈ keys <;> simp [reviseIndex, insertIndex, retractIndex, h]

/-- Untouched bindings retain exact row payloads and opaque callback identities. -/
theorem reviseIndex_frame (keys : List K) (project : K → V → I) (after : K → Option V)
    (cache : I → K → Option V) (bucket : I) (key : K) (outside : key ∉ keys) :
    reviseIndex keys project after cache bucket key = cache bucket key := by
  simp [reviseIndex_lookup, outside]

/-- Complete cache correlation is restored by changed-key processing alone. -/
theorem reviseIndex_correct (keys : List K) (project : K → V → I)
    (before after : K → Option V) (frame : ∀ key, key ∉ keys → after key = before key) :
    reviseIndex keys project after (indexView project before) = indexView project after := by
  funext bucket key
  by_cases h : key ∈ keys
  · simp [reviseIndex_lookup, h]
  · simp [reviseIndex_lookup, h, indexView, frame key h]

/-- Actual successful table deltas supply the required unchanged-key frame. -/
theorem reviseIndex_delta [DecidableEq V] (ops : TableCarrier K V A)
    (project : K → V → I) (edits : List (Change K V)) (before after : A)
    (success : ops.apply edits before = .ok after) :
    reviseIndex (edits.map Change.key) project (ops.read after)
      (indexView project (ops.read before)) = indexView project (ops.read after) := by
  apply reviseIndex_correct
  intro key outside
  apply applyChanges_frame edits (ops.read before) (ops.read after)
  · rw [← ops.apply_read, success]; rfl
  · intro change member same
    apply outside
    exact List.mem_map.mpr ⟨change, member, same.symm⟩

/-- Repeated keys need no separate mutable set or deduplication protocol. -/
theorem reviseIndex_duplicate (keys : List K) (project : K → V → I)
    (after : K → Option V) (cache : I → K → Option V) :
    reviseIndex (keys ++ keys) project after cache = reviseIndex keys project after cache := by
  funext bucket key
  simp only [reviseIndex_lookup, List.mem_append, or_self]

/-- A successful unique claim replaces one bucket or returns its exact two owners. -/
def claimIndex (owners : I → Option K) (bucket : I) (incoming : K) : Except (K × K) (I → Option K) :=
  match owners bucket with
  | none => .ok (replace owners bucket (some incoming))
  | some existing => if existing = incoming then .ok (replace owners bucket (some incoming))
      else .error (existing, incoming)

/-- Absence accepts a new unique owner. -/
theorem claimIndex_empty (owners : I → Option K) (bucket : I) (key : K)
    (empty : owners bucket = none) :
    claimIndex owners bucket key = .ok (replace owners bucket (some key)) := by simp [claimIndex, empty]

/-- Repeated final insertion of the same primary key does not create a conflict. -/
theorem claimIndex_same (owners : I → Option K) (bucket : I) (key : K)
    (same : owners bucket = some key) :
    claimIndex owners bucket key = .ok (replace owners bucket (some key)) := by simp [claimIndex, same]

/-- Competing owners retain the original cause rather than selecting a winner. -/
theorem claimIndex_conflict (owners : I → Option K) (bucket : I) (left right : K)
    (found : owners bucket = some left) (different : left ≠ right) :
    claimIndex owners bucket right = .error (left, right) := by simp [claimIndex, found, different]

/-- Finite multiple-key membership retains the exact admitted row payload.
This extends the collection future work; projection purity and carrier laws are premises. -/
def indexKeysView (project : K → V → List I) (primary : K → Option V)
    (bucket : I) (key : K) : Option V :=
  match primary key with
  | none => none
  | some row => if bucket ∈ project key row then some row else none

/-- Reuse the existing column retraction before restoring all final memberships. -/
def reviseIndexKeys (keys : List K) (project : K → V → List I) (after : K → Option V)
    (cache : I → K → Option V) : I → K → Option V :=
  fun bucket key => if key ∈ keys then indexKeysView project after bucket key
    else retractIndex keys cache bucket key

/-- Successful revision changes exactly the touched columns, for every bucket. -/
theorem reviseIndexKeys_lookup (keys : List K) (project : K → V → List I)
    (after : K → Option V) (cache : I → K → Option V) (bucket : I) (key : K) :
    reviseIndexKeys keys project after cache bucket key =
      if key ∈ keys then indexKeysView project after bucket key else cache bucket key := by
  by_cases h : key ∈ keys <;> simp [reviseIndexKeys, retractIndex, h]

/-- Changed-key installation restores all buckets without scanning untouched rows. -/
theorem reviseIndexKeys_correct (keys : List K) (project : K → V → List I)
    (before after : K → Option V) (frame : ∀ key, key ∉ keys → after key = before key) :
    reviseIndexKeys keys project after (indexKeysView project before) = indexKeysView project after := by
  funext bucket key
  by_cases h : key ∈ keys
  · simp [reviseIndexKeys_lookup, h]
  · simp [reviseIndexKeys_lookup, h, indexKeysView, frame key h]

/-- Existing delta installation supplies the frame required by multiple-key indexes. -/
theorem reviseIndexKeys_delta [DecidableEq V] (ops : TableCarrier K V A)
    (project : K → V → List I) (edits : List (Change K V)) (before after : A)
    (success : ops.apply edits before = .ok after) :
    reviseIndexKeys (edits.map Change.key) project (ops.read after)
      (indexKeysView project (ops.read before)) = indexKeysView project (ops.read after) := by
  apply reviseIndexKeys_correct
  intro key outside
  apply applyChanges_frame edits (ops.read before) (ops.read after)
  · rw [← ops.apply_read, success]; rfl
  · intro change member same
    apply outside
    exact List.mem_map.mpr ⟨change, member, same.symm⟩

/-- Duplicate projected keys do not change membership or opaque Function payloads. -/
theorem indexKeysView_duplicate (project : K → V → List I) (primary : K → Option V) :
    indexKeysView (fun key row => project key row ++ project key row) primary =
      indexKeysView project primary := by
  funext bucket key
  cases h : primary key <;> simp [indexKeysView, h]

/-- Stable membership-preserving deduplication changes no grouped observation. -/
theorem indexKeysView_membership (left right : K → V → List I) (primary : K → Option V)
    (same : ∀ key row bucket, bucket ∈ left key row ↔ bucket ∈ right key row) :
    indexKeysView left primary = indexKeysView right primary := by
  funext bucket key
  cases h : primary key with
  | none => simp [indexKeysView, h]
  | some row => simp [indexKeysView, h, same key row bucket]

/-- Single-key declarations are exactly the existing index protocol. -/
theorem indexKeysView_single (project : K → V → I) (primary : K → Option V) :
    indexKeysView (fun key row => [project key row]) primary = indexView project primary := by
  funext bucket key
  cases h : primary key <;> simp [indexKeysView, indexView, h, eq_comm]

/-- Ordered multiple-key claims reuse the existing owner rule and short-circuit
with the first conflicting key; no partially updated owners escape a failure. -/
def claimIndexKeys (owners : I → Option K) (buckets : List I) (key : K) :
    Except (I × (K × K)) (I → Option K) :=
  match buckets with
  | [] => .ok owners
  | bucket :: rest => match claimIndex owners bucket key with
    | .error conflict => .error (bucket, conflict)
    | .ok next => claimIndexKeys next rest key

/-- No memberships is a successful no-op, not an absent primary row. -/
theorem claimIndexKeys_empty (owners : I → Option K) (key : K) :
    claimIndexKeys owners [] key = .ok owners := rfl

/-- A conflicting head suppresses all later membership claims and retains its cause. -/
theorem claimIndexKeys_conflict (owners : I → Option K) (bucket : I) (rest : List I)
    (left right : K) (found : owners bucket = some left) (different : left ≠ right) :
    claimIndexKeys owners (bucket :: rest) right = .error (bucket, (left, right)) := by
  simp [claimIndexKeys, claimIndex_conflict owners bucket left right found different]

/-- A finite reference check compares projections while allowing repeated owner IDs. -/
def uniqueIndexRows (project : K → V → I) (rows : List (K × V)) : Bool :=
  rows.all fun left => rows.all fun right =>
    decide (project left.1 left.2 = project right.1 right.2 → left.1 = right.1)

/-- Finite acceptance establishes unique ownership for every enumerated row pair. -/
theorem uniqueIndexRows_sound (project : K → V → I) (rows : List (K × V))
    (valid : uniqueIndexRows project rows = true) (left right : K × V)
    (hl : left ∈ rows) (hr : right ∈ rows)
    (same : project left.1 left.2 = project right.1 right.2) : left.1 = right.1 := by
  have first := List.all_eq_true.mp valid left hl
  have second := List.all_eq_true.mp first right hr
  exact (of_decide_eq_true second) same

section Family
variable {IndexKey : N → Type} [∀ name, DecidableEq (IndexKey name)]

/-- Heterogeneous declarations share one primary but have independent key Types. -/
abbrev IndexViews (IndexKey : N → Type) (K V : Type) := ∀ name, IndexKey name → K → Option V

/-- Every named cache is the exact view of the same installed primary. -/
def correlatedViews (project : ∀ name, K → V → IndexKey name) (primary : K → Option V) :
    IndexViews IndexKey K V := fun name => indexView (project name) primary

/-- All indexes update in one pure staging result, with no intermediate publication. -/
def reviseIndexes (keys : List K) (project : ∀ name, K → V → IndexKey name)
    (after : K → Option V) (cache : IndexViews IndexKey K V) : IndexViews IndexKey K V :=
  fun name => reviseIndex keys (project name) after (cache name)

/-- Per-index correctness composes for any heterogeneous family. -/
theorem reviseIndexes_correct (keys : List K) (project : ∀ name, K → V → IndexKey name)
    (before after : K → Option V) (frame : ∀ key, key ∉ keys → after key = before key) :
    reviseIndexes keys project after (correlatedViews project before) = correlatedViews project after := by
  funext name
  exact reviseIndex_correct keys (project name) before after frame

/-- Declarations are checked in order; grouped indexes impose no uniqueness rule. -/
def checkIndexRows (names : List N) (unique : N → Bool)
    (project : ∀ name, K → V → IndexKey name) (rows : List (K × V)) : Except N Unit :=
  match names with
  | [] => .ok ()
  | name :: rest =>
    if unique name then
      if uniqueIndexRows (project name) rows then checkIndexRows rest unique project rows
      else .error name
    else checkIndexRows rest unique project rows

/-- The first declared failing unique index suppresses all later checks. -/
theorem checkIndexRows_first (name : N) (rest : List N) (unique : N → Bool)
    (project : ∀ name, K → V → IndexKey name) (rows : List (K × V))
    (required : unique name = true) (bad : uniqueIndexRows (project name) rows = false) :
    checkIndexRows (name :: rest) unique project rows = .error name := by
  simp [checkIndexRows, required, bad]

/-- A whole accepted declaration list satisfies every required finite uniqueness rule. -/
theorem checkIndexRows_sound (names : List N) (unique : N → Bool)
    (project : ∀ name, K → V → IndexKey name) (rows : List (K × V))
    (success : checkIndexRows names unique project rows = .ok ()) :
    ∀ name ∈ names, unique name = true → uniqueIndexRows (project name) rows = true := by
  induction names with
  | nil => simp
  | cons head rest ih =>
    cases flag : unique head <;> cases good : uniqueIndexRows (project head) rows <;>
      simp_all [checkIndexRows]

/-- A primary error or index refusal exposes no part of the staged whole snapshot. -/
def applyIndexed [DecidableEq V] (ops : TableCarrier K V A) (names : List N)
    (unique : N → Bool) (project : ∀ name, K → V → IndexKey name)
    (enumerate : A → List (K × V)) (edits : List (Change K V))
    (state : A × IndexViews IndexKey K V) : Except (Sum K N) (A × IndexViews IndexKey K V) :=
  ((ops.apply edits state.1).mapError Sum.inl).bind fun after =>
    ((checkIndexRows names unique project (enumerate after)).mapError Sum.inr).map fun _ =>
      (after, reviseIndexes (edits.map Change.key) project (ops.read after) state.2)

/-- Whole installation returns only caches correlated with the final primary. -/
theorem applyIndexed_correlated [DecidableEq V] (ops : TableCarrier K V A) (names : List N)
    (unique : N → Bool) (project : ∀ name, K → V → IndexKey name)
    (enumerate : A → List (K × V)) (edits : List (Change K V))
    (before after : A) (cache : IndexViews IndexKey K V)
    (success : applyIndexed ops names unique project enumerate edits
      (before, correlatedViews project (ops.read before)) = .ok (after, cache)) :
    cache = correlatedViews project (ops.read after) := by
  cases run : ops.apply edits before with
  | error key => simp [applyIndexed, run, Except.mapError, Except.bind] at success
  | ok next =>
    cases checked : checkIndexRows names unique project (enumerate next) with
    | error name => simp [applyIndexed, run, checked, Except.mapError, Except.bind, Except.map] at success
    | ok witness =>
      cases witness
      simp [applyIndexed, run, checked, Except.mapError, Except.bind, Except.map] at success
      rcases success with ⟨rfl, rfl⟩
      funext name
      exact reviseIndex_delta ops (project name) edits before next run

/-- A primary conflict wins before any declaration validation. -/
theorem applyIndexed_primary_failure [DecidableEq V] (ops : TableCarrier K V A) (names : List N)
    (unique : N → Bool) (project : ∀ name, K → V → IndexKey name)
    (enumerate : A → List (K × V)) (edits : List (Change K V))
    (state : A × IndexViews IndexKey K V) (key : K)
    (failed : ops.apply edits state.1 = .error key) :
    applyIndexed ops names unique project enumerate edits state = .error (.inl key) := by
  simp [applyIndexed, failed, Except.mapError, Except.bind]

/-- A late unique-index conflict exposes no staged primary or earlier cache. -/
theorem applyIndexed_unique_failure [DecidableEq V] (ops : TableCarrier K V A) (names : List N)
    (unique : N → Bool) (project : ∀ name, K → V → IndexKey name)
    (enumerate : A → List (K × V)) (edits : List (Change K V))
    (state : A × IndexViews IndexKey K V) (after : A) (name : N)
    (primary : ops.apply edits state.1 = .ok after)
    (failed : checkIndexRows names unique project (enumerate after) = .error name) :
    applyIndexed ops names unique project enumerate edits state = .error (.inr name) := by
  simp [applyIndexed, primary, failed, Except.mapError, Except.bind, Except.map]

/-- Complete backend enumeration turns finite accepted checks into logical unique
ownership for every primary row, without a finite global primary-key universe. -/
theorem checkIndexRows_ownership (names : List N) (unique : N → Bool)
    (project : ∀ name, K → V → IndexKey name) (rows : List (K × V)) (primary : K → Option V)
    (complete : ∀ key value, primary key = some value → (key, value) ∈ rows)
    (checked : checkIndexRows names unique project rows = .ok ())
    (name : N) (member : name ∈ names) (required : unique name = true)
    (left right : K) (lv rv : V) (hl : primary left = some lv) (hr : primary right = some rv)
    (same : project name left lv = project name right rv) : left = right :=
  uniqueIndexRows_sound (project name) rows
    (checkIndexRows_sound names unique project rows checked name member required)
    (left, lv) (right, rv) (complete left lv hl) (complete right rv hr) same

/-- A late index refusal retains the whole original state in every existing style. -/
theorem applyIndexed_style_failure [DecidableEq V] (ops : TableCarrier K V A) (names : List N)
    (unique : N → Bool) (project : ∀ name, K → V → IndexKey name)
    (enumerate : A → List (K × V)) (edits : List (Change K V))
    (state : A × IndexViews IndexKey K V) (style : TableStyle) (cause : Sum K N)
    (failure : applyIndexed ops names unique project enumerate edits state = .error cause) :
    styleStep style (some state) (applyIndexed ops names unique project enumerate edits) =
      (some state, .error (.callback cause)) := styleStep_failure _ _ _ _ failure
end Family

/-- Inverse primary installation restores observations even if tree shapes differ. -/
theorem indexed_primary_inverse [DecidableEq V] (ops : TableCarrier K V A)
    (edits : List (Change K V)) (before after restored : A)
    (forward : ops.apply edits before = .ok after)
    (backward : ops.apply (inverseChanges edits) after = .ok restored) : ops.read restored = ops.read before := by
  have h : applyChanges edits (ops.read before) = .ok (ops.read after) := by
    rw [← ops.apply_read, forward]; rfl
  have undo := applyChanges_inverse edits (ops.read before) (ops.read after) h
  have actual := ops.apply_read (inverseChanges edits) after
  rw [backward, undo] at actual
  exact Except.ok.inj actual

/-- Correct inverse caches restore every bucket/member observation as well. -/
theorem indexed_cache_inverse [DecidableEq V] (ops : TableCarrier K V A) (project : K → V → I)
    (edits : List (Change K V)) (before after restored : A)
    (forward : ops.apply edits before = .ok after)
    (backward : ops.apply (inverseChanges edits) after = .ok restored) :
    indexView project (ops.read restored) = indexView project (ops.read before) := by
  rw [indexed_primary_inverse ops edits before after restored forward backward]

/-- A pair-recursion certificate partitions aligned observations into shared
bindings, one changed binding, or ordered disjoint subtrees. A backend must supply
this alignment correctly; pointer identity alone is not a proof of immutability. -/
inductive DeltaTraversal (K V : Type) where
  | shared (rows : List (K × V))
  | changed (edit : Change K V)
  | fork (left right : DeltaTraversal K V)

/-- Reference events enumerate even unchanged bindings of a shared subtree. -/
def deltaTraversalEvents : DeltaTraversal K V → List (Change K V)
  | .shared rows => rows.map (fun row => ⟨row.1, some row.2, some row.2⟩)
  | .changed edit => [edit]
  | .fork left right => deltaTraversalEvents left ++ deltaTraversalEvents right

/-- The first phase emits old updates/deletions; a stored false is still present. -/
def deltaOldChanged [DecidableEq V] (edit : Change K V) : Bool :=
  edit.before.isSome && !decide (edit.before = edit.after)

/-- Only genuinely absent old bindings enter the second insertion phase. -/
def deltaNewInserted (edit : Change K V) : Bool := edit.before.isNone && edit.after.isSome

/-- A shared subtree has no changes, but its complete admission is not omitted. -/
def prunedDeltaPhase (accept : Change K V → Bool) : DeltaTraversal K V → List (Change K V)
  | .shared _ => []
  | .changed edit => if accept edit then [edit] else []
  | .fork left right => prunedDeltaPhase accept left ++ prunedDeltaPhase accept right

/-- Exact old-then-new ordering is retained even when insertions have smaller keys. -/
def prunedDelta [DecidableEq V] (tree : DeltaTraversal K V) : List (Change K V) :=
  prunedDeltaPhase deltaOldChanged tree ++ prunedDeltaPhase deltaNewInserted tree

/-- The generic callback order over the same aligned observation certificate. -/
def fullDelta [DecidableEq V] (tree : DeltaTraversal K V) : List (Change K V) :=
  (deltaTraversalEvents tree).filter deltaOldChanged ++
    (deltaTraversalEvents tree).filter deltaNewInserted

omit [DecidableEq K] in
/-- Pruning is sound whenever the chosen phase rejects every unchanged event. -/
theorem prunedDeltaPhase_correct (accept : Change K V → Bool)
    (unchanged : ∀ key row, accept ⟨key, some row, some row⟩ = false)
    (tree : DeltaTraversal K V) :
    prunedDeltaPhase accept tree = (deltaTraversalEvents tree).filter accept := by
  induction tree with
  | shared rows =>
    simp only [prunedDeltaPhase, deltaTraversalEvents]
    symm
    apply List.filter_eq_nil_iff.mpr
    intro edit member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    simp [unchanged]
  | changed edit => cases h : accept edit <;> simp [prunedDeltaPhase, deltaTraversalEvents, h]
  | fork left right ihLeft ihRight =>
    simp [prunedDeltaPhase, deltaTraversalEvents, List.filter_append, ihLeft, ihRight]

/-- Callback order and payloads coincide, not merely their final dictionary. -/
theorem prunedDelta_correct [DecidableEq V] (tree : DeltaTraversal K V) :
    prunedDelta tree = fullDelta tree := by
  simp only [prunedDelta, fullDelta]
  rw [prunedDeltaPhase_correct deltaOldChanged (by intros; simp [deltaOldChanged]),
      prunedDeltaPhase_correct deltaNewInserted (by intros; simp [deltaNewInserted])]

/-- Existing optimistic installation has identical success and exact first failure. -/
theorem prunedDelta_install [DecidableEq V] (tree : DeltaTraversal K V) (view : K → Option V) :
    applyChanges (prunedDelta tree) view = applyChanges (fullDelta tree) view := by
  rw [prunedDelta_correct]

/-- Existing inverse/retry semantics use the identical ordered edit sequence. -/
theorem prunedDelta_inverse [DecidableEq V] (tree : DeltaTraversal K V) :
    inverseChanges (prunedDelta tree) = inverseChanges (fullDelta tree) := by
  rw [prunedDelta_correct]

/-- One pair pass inspects a shared node once instead of all of its bindings. -/
def prunedDeltaWork : DeltaTraversal K V → Nat
  | .shared _ | .changed _ => 1
  | .fork left right => 1 + prunedDeltaWork left + prunedDeltaWork right

/-- The unpruned reference additionally inspects shared bindings. Backend key
lookup and compressed-node alignment costs are separate from this visitor model. -/
def fullDeltaWork : DeltaTraversal K V → Nat
  | .shared rows => 1 + rows.length
  | .changed _ => 1
  | .fork left right => 1 + fullDeltaWork left + fullDeltaWork right

omit [DecidableEq K] in
/-- Both traversals pay the same complete initial admission. Only change-discovery
work is reduced; this is not a wall-clock, GC or concrete Gerbil recursor proof. -/
theorem prunedDelta_work (tree : DeltaTraversal K V) (admission : Nat) :
    admission + 2 * prunedDeltaWork tree ≤ admission + 2 * fullDeltaWork tree := by
  have bounded : prunedDeltaWork tree ≤ fullDeltaWork tree := by
    induction tree with
    | shared rows => simp [prunedDeltaWork, fullDeltaWork]
    | changed edit => simp [prunedDeltaWork, fullDeltaWork]
    | fork left right ihLeft ihRight =>
      simp only [prunedDeltaWork, fullDeltaWork]; omega
  omega

/-- Constructor scopes grow from declarations to discovered backends and then
child/origin metadata. Supported edits admitted outside these nested scopes
cannot change an earlier recipe while a later computed declaration is read.
The protected-edit premise is supplied by the host object mutation discipline. -/
theorem indexPreparation_frame {Id Metadata : Type} [DecidableEq Id] [DecidableEq Metadata]
    (declarations backends origins : List Id) (edits : List (Change Id Metadata))
    (before after : Id → Option Metadata)
    (guarded : ∀ edit ∈ edits, edit.key ∉
      extendProtection origins (extendProtection backends declarations false) false)
    (accepted : applyChanges edits before = .ok after) :
    ∀ key ∈ declarations ++ backends ++ origins, after key = before key := by
  intro key member
  apply applyChanges_frame edits before after accepted key
  intro edit inside same
  apply guarded edit inside
  rw [mem_extendProtection origins _ false (by simp), List.mem_append,
      mem_extendProtection backends declarations false (by simp), List.mem_append]
  subst key
  simp only [List.mem_append] at member
  rcases member with (declaration | backend) | origin
  · exact Or.inr (Or.inr declaration)
  · exact Or.inr (Or.inl backend)
  · exact Or.inl origin

/-- Current source stamps after protected preparation still describe the original
captured recipes. No stamp sampled only after compilation can establish this
premise when getters were allowed to mutate previously compiled participants. -/
theorem indexPreparation_current {Id : Type} [DecidableEq Id]
    (declarations backends origins : List Id) (edits : List (Change Id Nat))
    (before after : Id → Option Nat)
    (guarded : ∀ edit ∈ edits, edit.key ∉
      extendProtection origins (extendProtection backends declarations false) false)
    (accepted : applyChanges edits before = .ok after) :
    stampMatches (declarations ++ backends ++ origins) before after = true := by
  simp only [stampMatches, List.all_eq_true]
  intro key member
  exact beq_iff_eq.mpr (indexPreparation_frame declarations backends origins edits
    before after guarded accepted key member).symm

/-- Four finite descriptor endpoints: tables carry key/value identities and
converters carry domain/codomain identities. No inference or predicate sampling
stands in for these exact identities. -/
def translationTypesAgree {Id Kind : Type} [DecidableEq Kind]
    (metadata : Id → Option (Kind × Kind)) (source target key value : Id) : Bool :=
  match metadata source, metadata target, metadata key, metadata value with
  | some (sk, sv), some (tk, tv), some (kd, kc), some (vd, vc) =>
      decide (kd = sk ∧ kc = tk ∧ vd = sv ∧ vc = tv)
  | _, _, _, _ => false

/-- Endpoint admission survives preparation only when the declaration participants
remain protected throughout getter/callback selection, not merely when stamps
sampled after preparation happen to be current. The supported-edit discipline and
faithful descriptor snapshots are host premises. -/
theorem translationPreparation_compatible {Id Kind : Type}
    [DecidableEq Id] [DecidableEq Kind]
    (source target key value : Id) (children origins : List Id)
    (edits : List (Change Id (Kind × Kind)))
    (before after : Id → Option (Kind × Kind))
    (guarded : ∀ edit ∈ edits, edit.key ∉
      extendProtection origins
        (extendProtection children [source, target, key, value] false) false)
    (accepted : applyChanges edits before = .ok after) :
    translationTypesAgree after source target key value =
      translationTypesAgree before source target key value := by
  have frame := indexPreparation_frame [source, target, key, value]
    children origins edits before after guarded accepted
  simp only [translationTypesAgree]
  rw [frame source (by simp), frame target (by simp),
      frame key (by simp), frame value (by simp)]

section CacheAdmission
variable {Name : Type} {Cache : Name → Type}

/-- Prepare and recognize each complete heterogeneous cache in declaration order.
A later preparation never starts after an earlier recognition refuses. Recognition
returns Unit so it cannot normalize or replace an admitted opaque cache payload. -/
def stageIndexCaches (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) :
    List Name → Except E (List (Sigma Cache))
  | [] => .ok []
  | name :: rest => match prepare name with
    | .error cause => .error cause
    | .ok cache => match admit name cache with
      | .error cause => .error cause
      | .ok () => match stageIndexCaches prepare admit rest with
        | .error cause => .error cause
        | .ok prepared => .ok (⟨name, cache⟩ :: prepared)

/-- Backend/projector failure precedes the current cache recognizer and all later
recipes. Both the original cause and lack of a partial return are preserved. -/
theorem stageIndexCaches_prepare_refused (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) (name : Name) (rest : List Name) (cause : E)
    (refused : prepare name = .error cause) :
    stageIndexCaches prepare admit (name :: rest) = .error cause := by
  simp [stageIndexCaches, refused]

/-- A whole-cache refusal takes precedence over every later recipe, even after
this recipe's persistent backend finished constructing a well-shaped cache. -/
theorem stageIndexCaches_admit_refused (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) (name : Name) (rest : List Name)
    (cache : Cache name) (cause : E) (built : prepare name = .ok cache)
    (refused : admit name cache = .error cause) :
    stageIndexCaches prepare admit (name :: rest) = .error cause := by
  simp [stageIndexCaches, built, refused]

/-- Accepted entries have exactly the requested declaration names and order. -/
theorem stageIndexCaches_names (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) (names : List Name)
    (prepared : List (Sigma Cache)) (success : stageIndexCaches prepare admit names = .ok prepared) :
    prepared.map Sigma.fst = names := by
  induction names generalizing prepared with
  | nil => simp [stageIndexCaches] at success; subst prepared; rfl
  | cons name rest ih =>
    cases hp : prepare name with
    | error cause => simp [stageIndexCaches, hp] at success
    | ok cache =>
      cases ha : admit name cache with
      | error cause => simp [stageIndexCaches, hp, ha] at success
      | ok done =>
        cases done
        cases ht : stageIndexCaches prepare admit rest with
        | error cause => simp [stageIndexCaches, hp, ha, ht] at success
        | ok tail =>
          simp [stageIndexCaches, hp, ha, ht] at success
          subst prepared
          simp [ih tail ht]

/-- Every published cache passed its OWN complete Type recognizer. This includes
recursive bucket constraints when grouped caches store primary-table values. -/
theorem stageIndexCaches_admitted (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) (names : List Name)
    (prepared : List (Sigma Cache)) (success : stageIndexCaches prepare admit names = .ok prepared) :
    ∀ entry ∈ prepared, admit entry.1 entry.2 = .ok () := by
  induction names generalizing prepared with
  | nil => simp [stageIndexCaches] at success; subst prepared; simp
  | cons name rest ih =>
    cases hp : prepare name with
    | error cause => simp [stageIndexCaches, hp] at success
    | ok cache =>
      cases ha : admit name cache with
      | error cause => simp [stageIndexCaches, hp, ha] at success
      | ok done =>
        cases done
        cases ht : stageIndexCaches prepare admit rest with
        | error cause => simp [stageIndexCaches, hp, ha, ht] at success
        | ok tail =>
          simp [stageIndexCaches, hp, ha, ht] at success
          subst prepared
          intro entry member
          rcases List.mem_cons.mp member with same | later
          · subst entry; exact ha
          · exact ih tail ht entry later

/-- Successful staging has one admitted entry per declaration. Recognition cost
itself can scan the full cache or buckets; this is not an O(delta) time bound. -/
theorem stageIndexCaches_length (prepare : ∀ name, Except E (Cache name))
    (admit : ∀ name, Cache name → Except E Unit) (names : List Name)
    (prepared : List (Sigma Cache)) (success : stageIndexCaches prepare admit names = .ok prepared) :
    prepared.length = names.length := by
  have same := congrArg List.length (stageIndexCaches_names prepare admit names prepared success)
  simpa using same

/-- Publish one original primary with the complete admitted cache family. Cold
construction and warm revision use this same boundary after primary admission. -/
def publishIndexCaches (primary : A) (names : List Name)
    (prepare : ∀ name, Except E (Cache name)) (admit : ∀ name, Cache name → Except E Unit) :
    Except E (A × List (Sigma Cache)) :=
  (stageIndexCaches prepare admit names).map (primary, ·)

/-- No primary or earlier prepared cache is returned when any family stage fails. -/
theorem publishIndexCaches_refused (primary : A) (names : List Name)
    (prepare : ∀ name, Except E (Cache name)) (admit : ∀ name, Cache name → Except E Unit)
    (cause : E) (refused : stageIndexCaches prepare admit names = .error cause) :
    publishIndexCaches primary names prepare admit = .error cause := by
  simp [publishIndexCaches, refused, Except.map]

/-- Admission retains exact primary/cache identities; it does not rebuild them
or disturb correlation already established by the persistent index installer. -/
theorem publishIndexCaches_ready (primary : A) (names : List Name)
    (prepare : ∀ name, Except E (Cache name)) (admit : ∀ name, Cache name → Except E Unit)
    (prepared : List (Sigma Cache)) (ready : stageIndexCaches prepare admit names = .ok prepared) :
    publishIndexCaches primary names prepare admit = .ok (primary, prepared) := by
  simp [publishIndexCaches, ready, Except.map]

/-- A cold or warm family failure leaves every owned presentation's old complete
snapshot available for explicit retry. External callback effects are not modeled. -/
theorem publishIndexCaches_style_refused (style : TableStyle) (primary : A)
    (before : A × List (Sigma Cache)) (names : List Name)
    (prepare : ∀ name, Except E (Cache name)) (admit : ∀ name, Cache name → Except E Unit)
    (cause : E) (refused : stageIndexCaches prepare admit names = .error cause) :
    styleStep style (some before) (fun _ => publishIndexCaches primary names prepare admit) =
      (some before, .error (.callback cause)) :=
  styleStep_failure style before _ cause (publishIndexCaches_refused primary names prepare admit cause refused)

end CacheAdmission


section BackendKeyWork
variable {R : Type}

/-- Reference work scheduler for a backend's explicit logical key map. It keeps
first physical representatives; membership checks reuse the backend equivalence.
This finite list oracle specifies semantics, not the registry's runtime cost. -/
def distinctKeyWork (logical : R → K) (seen : List K) : List R → List R
  | [] => []
  | head :: tail =>
    if logical head ∈ seen then distinctKeyWork logical seen tail
    else head :: distinctKeyWork logical (logical head :: seen) tail

/-- Every unvisited backend key class remains represented, and no visited class
is scheduled again. Physical aliases need not be structurally equal. -/
theorem distinctKeyWork_mem (logical : R → K) (rows : List R) (seen : List K) (key : K) :
    key ∈ (distinctKeyWork logical seen rows).map logical ↔
      key ∈ rows.map logical ∧ key ∉ seen := by
  induction rows generalizing seen with
  | nil => simp [distinctKeyWork]
  | cons head tail ih =>
    by_cases visited : logical head ∈ seen
    · simp only [distinctKeyWork, if_pos visited, ih, List.map_cons, List.mem_cons]
      constructor
      · intro h; exact ⟨Or.inr h.1, h.2⟩
      · rintro ⟨same | later, fresh⟩
        · subst key; exact False.elim (fresh visited)
        · exact ⟨later, fresh⟩
    · simp only [distinctKeyWork, if_neg visited, List.map_cons, List.mem_cons, ih]
      by_cases same : key = logical head <;> simp_all

/-- Exactly one representative per logical class reaches cache construction. -/
theorem distinctKeyWork_nodup (logical : R → K) (rows : List R) (seen : List K) :
    ((distinctKeyWork logical seen rows).map logical).Nodup := by
  induction rows generalizing seen with
  | nil => simp [distinctKeyWork]
  | cons head tail ih =>
    by_cases visited : logical head ∈ seen
    · simpa [distinctKeyWork, visited] using ih seen
    · simp only [distinctKeyWork, if_neg visited, List.map_cons, List.nodup_cons]
      exact ⟨by simp [distinctKeyWork_mem], ih _⟩

/-- Scheduling is bounded by submitted edits. This does not bound backend lookup,
recognition, allocation, or callback cost; those remain separately charged. -/
theorem distinctKeyWork_length (logical : R → K) (rows : List R) (seen : List K) :
    (distinctKeyWork logical seen rows).length ≤ rows.length := by
  induction rows generalizing seen with
  | nil => simp [distinctKeyWork]
  | cons head tail ih =>
    by_cases visited : logical head ∈ seen
    · simp only [distinctKeyWork, if_pos visited, List.length_cons]
      exact Nat.le_trans (ih seen) (Nat.le_succ _)
    · simpa [distinctKeyWork, visited] using Nat.succ_le_succ (ih (logical head :: seen))

/-- A fresh worklist keeps the first submitted physical representative. -/
theorem distinctKeyWork_first (logical : R → K) (head : R) (tail : List R) :
    distinctKeyWork logical [] (head :: tail) =
      head :: distinctKeyWork logical [logical head] tail := by simp [distinctKeyWork]

/-- Grouped index observations are unchanged by backend-key coalescing, assuming
primary lookup and classification factor through that explicit logical key. -/
theorem reviseIndexKeys_distinctWork (logical : R → K) (rows : List R)
    (project : K → V → List I) (after : K → Option V) (cache : I → K → Option V) :
    reviseIndexKeys ((distinctKeyWork logical [] rows).map logical) project after cache =
      reviseIndexKeys (rows.map logical) project after cache := by
  funext bucket key
  simp [reviseIndexKeys_lookup, distinctKeyWork_mem]

/-- Coalescing only schedules work AFTER the unchanged sequential installer.
Every intermediate expectation remains in the input; no delta is squashed. -/
def installIndexWork [DecidableEq V] (ops : TableCarrier K V A)
    (edits : List (Change K V)) (before : A) : Except K (A × List K) :=
  (ops.apply edits before).map fun after =>
    (after, distinctKeyWork id [] (edits.map Change.key))

/-- An intermediate conflict refuses the whole preparation, even when the edits
would cancel at the final snapshot. No cache work or successor is returned. -/
theorem installIndexWork_refused [DecidableEq V] (ops : TableCarrier K V A)
    (edits : List (Change K V)) (before : A) (cause : K)
    (refused : ops.apply edits before = .error cause) :
    installIndexWork ops edits before = .error cause := by
  simp [installIndexWork, refused, Except.map]

end BackendKeyWork

/-- A grouped bucket is rebuilt from its final finite bindings. Missing work
reuses the old bucket; empty work deletes it without evaluating a business empty
constructor. Scratch key-space fidelity and the finite builder laws are premises. -/
def materializeIndexBucket (build : List Row → Except E A)
    (original : Option A) (work : Option (List Row)) : Except E (Option A) :=
  match work with
  | none => .ok original
  | some [] => .ok none
  | some (row :: rest) => (build (row :: rest)).map some

/-- Untouched buckets keep their exact identity, including opaque Functions. -/
theorem materializeIndexBucket_untouched (build : List Row → Except E A)
    (original : Option A) : materializeIndexBucket build original none = .ok original := rfl

/-- Removing the final member requires no valid empty business value or builder. -/
theorem materializeIndexBucket_deleted (build : List Row → Except E A)
    (original : Option A) : materializeIndexBucket build original (some []) = .ok none := rfl

/-- Only the complete nonempty bucket is passed to the existing constructor. -/
theorem materializeIndexBucket_ready (build : List Row → Except E A)
    (original : Option A) (row : Row) (rest : List Row) (bucket : A)
    (ready : build (row :: rest) = .ok bucket) :
    materializeIndexBucket build original (some (row :: rest)) = .ok (some bucket) := by
  simp [materializeIndexBucket, ready, Except.map]

/-- Constructor refusal returns its original cause, without exposing scratch data. -/
theorem materializeIndexBucket_refused (build : List Row → Except E A)
    (original : Option A) (row : Row) (rest : List Row) (cause : E)
    (refused : build (row :: rest) = .error cause) :
    materializeIndexBucket build original (some (row :: rest)) = .error cause := by
  simp [materializeIndexBucket, refused, Except.map]

/-- Accepted finite constructors imply each newly materialized business bucket
satisfies its complete invariant. Intermediate scratch groups need not satisfy it. -/
theorem materializeIndexBucket_admitted (build : List Row → Except E A)
    (admit : A → Prop) (law : ∀ rows bucket, build rows = .ok bucket → admit bucket)
    (original : Option A) (row : Row) (rest : List Row) (bucket : A)
    (ready : materializeIndexBucket build original (some (row :: rest)) = .ok (some bucket)) :
    admit bucket := by
  cases built : build (row :: rest) with
  | error cause => simp [materializeIndexBucket, built, Except.map] at ready
  | ok value =>
    simp [materializeIndexBucket, built, Except.map] at ready
    subst value
    exact law _ _ built

/-- Exact final row delivery preserves the existing changed-key index relation.
This is conditional on faithful scratch enumeration, not a proof of a host tree. -/
theorem materializeIndexBucket_rows (build : List Row → Except E A)
    (read : A → List Row) (law : ∀ rows bucket, build rows = .ok bucket → read bucket = rows)
    (original : Option A) (row : Row) (rest : List Row) (bucket : A)
    (ready : build (row :: rest) = .ok bucket) :
    materializeIndexBucket build original (some (row :: rest)) = .ok (some bucket) ∧
      read bucket = row :: rest := ⟨materializeIndexBucket_ready _ _ _ _ _ ready, law _ _ ready⟩

/-- Preparation charges every affected finite bucket, with no work for untouched
or deleted buckets. Registry setup, old-bucket copying, admission and backend
construction costs are additional parameters, not hidden VM speedup claims. -/
def indexBucketRowWork (work : Option (List Row)) : Nat :=
  match work with | none => 0 | some rows => rows.length

/-- Unaffected buckets introduce neither finite construction nor row-delivery work. -/
theorem indexBucketRowWork_untouched : indexBucketRowWork (Row := Row) none = 0 := rfl

/-- Finite reconstruction charges all final rows, not merely the changed keys. -/
theorem indexBucketRowWork_affected (rows : List Row) :
    indexBucketRowWork (some rows) = rows.length := rfl

end LeanPoo.Functional.OrderedDictionary
