import LeanPoo.Prototype.RepresentationIndex
import LeanPoo.Prototype.RepresentationNames

/-! Effective declaration indexes and guarded visibility preparation.
String keys injectively denote Symbol identities. Private persistent storage,
standard first-entry indexed lookup, registered descriptor/source edges and serial
supported edits are host premises. No physical heap, RBTree balancing, arbitrary
callback purity/termination or machine-time theorem is asserted here. -/
namespace LeanPoo.Prototype.Representation

/-- Keep the first C3 declaration of each name, even when that descriptor is hidden. -/
def selectDeclarations (entries : List (String × Value)) (seen : List String := []) : List (String × Value) :=
  match entries with
  | [] => []
  | entry :: tail => if entry.1 ∈ seen then selectDeclarations tail seen
      else entry :: selectDeclarations tail (entry.1 :: seen)

/-- First-occurrence selection preserves the actual descriptor, including false/functions. -/
theorem first_selectDeclarations (entries : List (String × Value)) (seen : List String)
    (name : String) (fresh : name ∉ seen) :
    first (selectDeclarations entries seen) name = first entries name := by
  induction entries generalizing seen with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    by_cases present : key ∈ seen
    · have different : key ≠ name := fun same => fresh (same ▸ present)
      simp [selectDeclarations, first, present, different, ih seen fresh]
    · by_cases same : key = name
      · subst key; simp [selectDeclarations, first, fresh]
      · have next : name ∉ key :: seen := by simp [Ne.symm same, fresh]
        simp [selectDeclarations, first, present, same, ih (key :: seen) next]

/-- Seen names never reappear, so a hidden override cannot expose its ancestor. -/
theorem selectDeclarations_excludes (entries : List (String × Value)) (seen : List String)
    (name : String) (present : name ∈ seen) :
    ∀ entry ∈ selectDeclarations entries seen, entry.1 ≠ name := by
  induction entries generalizing seen with
  | nil => simp [selectDeclarations]
  | cons head tail ih =>
    by_cases known : head.1 ∈ seen
    · simpa [selectDeclarations, known] using ih seen present
    · simp only [selectDeclarations, known, ↓reduceIte, List.mem_cons]
      intro entry member
      rcases member with same | rest
      · subst entry; exact fun same => known (same.symm ▸ present)
      · exact ih (head.1 :: seen) (by simp [present]) entry rest

/-- Merge ordered C3 roots by private traversal, then reuse first-name selection.
The host standard builder exports no private entry handles and captures results. -/
def mergeCatalogs (compact : Bool) (roots : List (Storage Value)) : Storage Value :=
  packWith compact (selectDeclarations (roots.flatMap Storage.entries))

/-- A snapshot/append input has the same ordered entries as private traversal.
Host copying/isolation and standard hash deduplication remain explicit premises. -/
theorem mergeCatalogs_snapshot (compact : Bool) (roots : List (Storage Value)) :
    mergeCatalogs compact roots = packWith compact
      (selectDeclarations (roots.flatMap (fun root => root.entries.map (fun entry => (entry.1, entry.2))))) := by
  simp [mergeCatalogs]

/-- Cross-root duplicates retain the first descriptor, including false/functions. -/
theorem mergeCatalogs_first (compact : Bool) (roots : List (Storage Value)) (name : String) :
    first (mergeCatalogs compact roots).entries name =
      first (roots.flatMap Storage.entries) name := by
  simp only [mergeCatalogs, entries_packWith]
  exact first_selectDeclarations _ [] name (by simp)

/-- Backend policy cannot change merge order, priority or payloads. -/
theorem mergeCatalogs_policy (roots : List (Storage Value)) :
    (mergeCatalogs true roots).entries = (mergeCatalogs false roots).entries := by
  simp [mergeCatalogs, entries_packWith]

/-- Count only public input spine/pair cells versus one private builder spine.
Deduplication, append copies, output capture, roots, backend storage and GC are
separate costs; this does not assert total heap allocation or machine time. -/
def mergeInputCells (direct : Bool) (roots : List (Storage Value)) : Nat :=
  (if direct then 1 else 2) * (roots.map (fun root => root.entries.length)).sum

/-- Direct input collection saves at least the duplicated input entry-pair stream
in this accounting, even before omitted baseline append copying is charged. -/
theorem mergeInputCells_saving (roots : List (Storage Value)) :
    mergeInputCells false roots - mergeInputCells true roots =
      (roots.map (fun root => root.entries.length)).sum := by
  simp [mergeInputCells]; omega

/-- Gerbil foldr checks the rightmost visibility first. Refusal stops before any
remaining earlier descriptor, and returns no partially visible public directory. -/
def checkVisibility (hidden : Value → Except E Bool) :
    List (String × Value) → Except E (List (String × Value))
  | [] => .ok []
  | head :: tail => match checkVisibility hidden tail with
    | .error cause => .error cause
    | .ok rest => match hidden head.2 with
      | .error cause => .error cause
      | .ok true => .ok rest
      | .ok false => .ok (head :: rest)

/-- Current visibility sees identical ordered descriptors and exact failures under
both storage policies; merging itself does not invoke metadata callbacks. -/
theorem mergeCatalogs_visibility (roots : List (Storage Value)) (hidden : Value → Except E Bool) :
    checkVisibility hidden (mergeCatalogs true roots).entries =
      checkVisibility hidden (mergeCatalogs false roots).entries := by
  rw [mergeCatalogs_policy]

/-- A right-hand refusal has precedence over the earlier descriptor's callback. -/
theorem checkVisibility_tail_refused (hidden : Value → Except E Bool)
    (head : String × Value) (tail : List (String × Value)) (cause : E)
    (refused : checkVisibility hidden tail = .error cause) :
    checkVisibility hidden (head :: tail) = .error cause := by simp [checkVisibility, refused]

/-- Exact descriptor refusal survives even after successful private tail preparation. -/
theorem checkVisibility_head_refused (hidden : Value → Except E Bool)
    (head : String × Value) (tail rest : List (String × Value)) (cause : E)
    (ready : checkVisibility hidden tail = .ok rest) (refused : hidden head.2 = .error cause) :
    checkVisibility hidden (head :: tail) = .error cause := by simp [checkVisibility, ready, refused]

/-- Observers always execute the current ordered visibility preparation. Only an
unobserved query may reuse a successful private directory of the current revision. -/
def chooseVisible (observed : Bool) (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value))) : Except E (List (String × Value)) :=
  if observed then prepare () else match cached with
    | some entries => .ok entries
    | none => prepare ()

/-- A warm cache never suppresses observed reads, callbacks, dependencies or refusal. -/
theorem chooseVisible_observed (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value))) :
    chooseVisible true cached prepare = prepare () := rfl

/-- Cache fidelity is an explicit source/invalidation premise, never inferred
from a prior successful Type check. Under it, both routes observe the same directory. -/
theorem chooseVisible_faithful (observed : Bool) (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value)))
    (faithful : ∀ saved, cached = some saved → prepare () = .ok saved) :
    chooseVisible observed cached prepare = prepare () := by
  cases observed with
  | true => rfl
  | false =>
    cases cached with
    | none => rfl
    | some saved => simpa [chooseVisible] using (faithful saved rfl).symm

/-- An empty private directory is a successful cache value, distinct from no cache. -/
theorem chooseVisible_empty (prepare : Unit → Except E (List (String × Value))) :
    chooseVisible false (some []) prepare = .ok [] := rfl

/-- The post-callback fence runs after descriptor preparation, before publication.
Its source revision is also bound into the existing owner-names observation. -/
def finishVisibility (before after : Nat) (prepared : Except String Value) :
    Except String Value :=
  match prepared with
  | .error cause => .error cause
  | .ok entries => if before = after then .ok entries else .error "object changed during declaration reflection"

/-- Original getter refusal has precedence over the post-callback revision fence. -/
theorem finishVisibility_refused (before after : Nat) (cause : String) :
    finishVisibility before after (.error cause : Except String (List (String × Value))) = .error cause := rfl

/-- A revision change cannot publish even a completely prepared public directory. -/
theorem finishVisibility_stale (before after : Nat) (entries : List (String × Value))
    (changed : before ≠ after) :
    finishVisibility before after (.ok entries) = .error "object changed during declaration reflection" := by
  simp [finishVisibility, changed]

/-- A fresh retry with stable current sources preserves the complete prepared directory. -/
theorem finishVisibility_retry (current : Nat) (entries : List (String × Value)) :
    finishVisibility current current (.ok entries) = .ok entries := by simp [finishVisibility]

/-- The same post-callback fence also closes concrete Slot admission. Only a
current successful value can reach an installer; this is not effect rollback. -/
def publishDeclaredValue (before after : Nat) (checked : Except String Value)
    (install : Value → Except String State) : Except String State :=
  (finishVisibility before after checked).bind install

/-- An original validation failure outranks a concurrent revision mismatch. -/
theorem publishDeclaredValue_refused (before after : Nat) (cause : String)
    (install : Value → Except String State) :
    publishDeclaredValue before after (.error cause) install = .error cause := rfl

/-- Even successful validation cannot reach installation after source invalidation. -/
theorem publishDeclaredValue_stale (before after : Nat) (value : Value)
    (install : Value → Except String State) (changed : before ≠ after) :
    publishDeclaredValue before after (.ok value) install =
      .error "object changed during declaration reflection" := by
  simp [publishDeclaredValue, finishVisibility, changed, Except.bind]

/-- A fresh stable request preserves the exact installed result or original error. -/
theorem publishDeclaredValue_retry (current : Nat) (value : Value)
    (install : Value → Except String State) :
    publishDeclaredValue current current (.ok value) install = install value := by
  simp [publishDeclaredValue, finishVisibility, Except.bind]

/-- Refused installation retains the post-callback state, not a fictitious
rollback of earlier user effects. No object publication follows a stale check. -/
theorem publishDeclaredValue_stale_frame (before after : Nat) (value : Value)
    (postCallback : State) (install : Value → Except String State)
    (changed : before ≠ after) :
    Object.publishEdit postCallback (publishDeclaredValue before after (.ok value) install) =
      postCallback := by
  rw [publishDeclaredValue_stale before after value install changed]
  rfl

/-- Logical work for a successfully selected public field; missing/metadata refusal
stops before value admission. Construction/capture, standard tree probes, concrete
value demand/check, owned exports, observers and GC are separate real costs. -/
structure DeclarationWork where
  merges : Nat
  visibilityPasses : Nat
  valueChecks : Nat
  deriving DecidableEq, Repr

/-- Membership and visibility have independent cold state; value admission is per call. -/
def declarationWork (observed fullReady visibleReady : Bool) : DeclarationWork :=
  ⟨if fullReady then 0 else 1, if observed || !visibleReady then 1 else 0, 1⟩

/-- A warm unobserved point query removes preparation, never the concrete Type check. -/
theorem declarationWork_warm : declarationWork false true true = ⟨0, 0, 1⟩ := rfl

/-- Observation still pays visibility preparation; cold queries pay both preparations. -/
theorem declarationWork_observed_cold :
    declarationWork true true true = ⟨0, 1, 1⟩ ∧
    declarationWork false false false = ⟨1, 1, 1⟩ := ⟨rfl, rfl⟩

/-- With unique keys disjoint from earlier roots, first selection is unchanged. -/
theorem selectDeclarations_unique (entries : List (String × Value)) (seen : List String)
    (unique : (entryKeys entries).Nodup)
    (fresh : ∀ name ∈ entryKeys entries, name ∉ seen) :
    selectDeclarations entries seen = entries := by
  induction entries generalizing seen with
  | nil => rfl
  | cons head tail ih =>
    have uniq := List.nodup_cons.mp unique
    have firstFresh := fresh head.1 (by simp [entryKeys])
    have restFresh : ∀ name ∈ entryKeys tail, name ∉ head.1 :: seen := by
      intro name member
      have old := fresh name (by simp [entryKeys] at member ⊢; exact Or.inr member)
      have different : name ≠ head.1 := by
        intro same
        exact uniq.1 (same ▸ member)
      simp [different, old]
    simp only [selectDeclarations, firstFresh, ↓reduceIte]
    rw [ih (head.1 :: seen) uniq.2 restFresh]

/-- A unique retained root has exactly the effective first-declaration observation. -/
theorem soleCatalog_reuse (root : Storage Value) (unique : (entryKeys root.entries).Nodup) :
    (packWith true root.entries).entries = selectDeclarations root.entries := by
  rw [entries_packWith, selectDeclarations_unique root.entries [] unique]
  simp

/-- Successful ordered visibility filtering only removes entries. -/
theorem checkVisibility_sublist (hidden : Value → Except E Bool)
    (entries accepted : List (String × Value)) (ready : checkVisibility hidden entries = .ok accepted) :
    accepted.Sublist entries := by
  induction entries generalizing accepted with
  | nil => simpa [checkVisibility] using ready
  | cons head tail ih =>
    cases tailReady : checkVisibility hidden tail with
    | error cause => simp [checkVisibility, tailReady] at ready
    | ok rest =>
      have sub := ih rest tailReady
      cases headReady : hidden head.2 with
      | error cause => simp [checkVisibility, tailReady, headReady] at ready
      | ok masked =>
        cases masked with
        | true =>
          have same : rest = accepted := by simpa [checkVisibility, tailReady, headReady] using ready
          subst accepted
          exact List.Sublist.cons _ sub
        | false =>
          have same : head :: rest = accepted := by simpa [checkVisibility, tailReady, headReady] using ready
          subst accepted
          exact List.Sublist.cons_cons _ sub

/-- Equal retained count proves all-pass identity, not just equal cardinality. -/
theorem checkVisibility_all_pass (hidden : Value → Except E Bool)
    (entries accepted : List (String × Value)) (ready : checkVisibility hidden entries = .ok accepted)
    (sameLength : accepted.length = entries.length) : accepted = entries :=
  (checkVisibility_sublist hidden entries accepted ready).eq_of_length sameLength

/-- Reuse an unchanged private root after successful visibility and its revision
fence. Count equality is used only with the filtering/sublist invariant above. -/
def filteredCatalog (root : Storage Value) (accepted : List (String × Value)) : Storage Value :=
  if accepted.length = root.entries.length then root else packWith root.compact accepted

/-- Root sharing preserves every payload and order, including false and Functions. -/
theorem filteredCatalog_observation (root : Storage Value) (hidden : Value → Except E Bool)
    (accepted : List (String × Value)) (ready : checkVisibility hidden root.entries = .ok accepted) :
    (filteredCatalog root accepted).entries = accepted := by
  unfold filteredCatalog
  split
  · exact (checkVisibility_all_pass hidden root.entries accepted ready ‹_›).symm
  · exact entries_packWith _ _

/-- All-pass filtering shares the root without weakening the post-callback fence. -/
theorem filteredCatalog_all_pass (root : Storage Value) : filteredCatalog root root.entries = root := by
  simp [filteredCatalog]

/-- Logical rebuilds, excluding input capture, uniqueness/visibility scans,
private snapshots, callback work, receiver state and GC. -/
def catalogRebuilds (soleUnique allVisible : Bool) : Nat :=
  (if soleUnique then 0 else 1) + (if allVisible then 0 else 1)

/-- The common unique/all-visible cold case avoids both full map builders. -/
theorem catalogRebuilds_reused : catalogRebuilds true true = 0 := rfl

/-- Partial visibility and multi-root merging still pay the required builders. -/
theorem catalogRebuilds_partial : catalogRebuilds true false = 1 ∧ catalogRebuilds false false = 2 := ⟨rfl,rfl⟩

/-- Policy-only conversion of a retained large standard tree copies no entry
stream. This is a source operation count, not a physical zero-allocation claim. -/
def policyEntryCopies (entries : Nat) (samePolicy sameBackend : Bool) : Nat :=
  if samePolicy || sameBackend then 0 else entries

/-- Large tree-policy views avoid export/recapture; bounded backend changes pay. -/
theorem policyEntryCopies_views (entries : Nat) :
    policyEntryCopies entries false true = 0 ∧ policyEntryCopies entries false false = entries := ⟨rfl,rfl⟩

/-- Standard reverse folds read private entries without exporting entry pairs.
The storage traversal order is a host premise; callbacks keep the same Except
refusal order as the original visibility specification. -/
def foldVisibility (hidden : Value → Except E Bool) (entries : List (String × Value)) :
    Except E (List (String × Value)) :=
  entries.foldrM (fun entry rest => do
    let masked ← hidden entry.2
    pure (if masked then rest else entry :: rest)) []

/-- Direct reverse folding preserves retained order and the exact first refusal. -/
theorem foldVisibility_eq (hidden : Value → Except E Bool) (entries : List (String × Value)) :
    foldVisibility hidden entries = checkVisibility hidden entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    simp only [foldVisibility, List.foldrM_cons] at ih ⊢
    rw [ih]
    cases tailReady : checkVisibility hidden tail with
    | error cause => simp [checkVisibility, tailReady, bind, Except.bind]
    | ok rest =>
      cases headReady : hidden head.2 with
      | error cause => simp [checkVisibility, tailReady, headReady, bind, Except.bind]
      | ok masked => cases masked <;> simp [checkVisibility, tailReady, headReady, bind, Except.bind, pure, Except.pure]

/-- Exporting before filtering allocates an owned spine and owned entry pairs;
direct private folds need neither. Result spines, partial-map capture, callback
work and GC are deliberately excluded from this logical export-cell count. -/
def visibilityExportCells (count : Nat) (direct : Bool) : Nat :=
  if direct then 0 else 2 * count

/-- Direct folds eliminate only the input export, regardless of visibility. -/
theorem visibilityExportCells_direct (count : Nat) :
    visibilityExportCells count true = 0 ∧ visibilityExportCells count false = 2 * count := ⟨rfl, rfl⟩

end LeanPoo.Prototype.Representation
