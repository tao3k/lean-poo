import Std

namespace ModuleCatalog

variable {Name Version Source Dependency : Type}

structure Row (Version Source : Type) where
  version : Version
  source : Source
  deriving DecidableEq

abbrev Catalog (Name Version Source : Type) := Name → List (Row Version Source)

def write [DecidableEq Name] (base : Catalog Name Version Source)
    (name : Name) (rows : List (Row Version Source)) : Catalog Name Version Source :=
  fun key => if key = name then rows else base key

def publish [DecidableEq Name] (base : Catalog Name Version Source)
    (edits : List (Name × List (Row Version Source))) : Catalog Name Version Source :=
  edits.foldl (fun prior (key, rows) => write prior key rows) base

theorem untouched [DecidableEq Name] (base : Catalog Name Version Source)
    (edits : List (Name × List (Row Version Source))) (key : Name)
    (noEdit : key ∉ edits.map Prod.fst) : publish base edits key = base key := by
  induction edits generalizing base with
  | nil => rfl
  | cons edit tail ih =>
    obtain ⟨name, rows⟩ := edit
    simp only [List.map_cons, List.mem_cons, not_or] at noEdit
    simpa [publish, write, noEdit.1] using ih (write base name rows) noEdit.2

def lookupEdit [DecidableEq Name] (key : Name) : List (Name × List (Row Version Source)) →
    Option (List (Row Version Source))
  | [] => none
  | (name, rows) :: tail => (lookupEdit key tail).orElse (fun _ => if key = name then some rows else none)

-- The persistent overlay agrees with cold lookup (including an empty bucket
-- retirement and repeated writes to the same name in a normalized sequence).
theorem cold_equivalence [DecidableEq Name] (base : Catalog Name Version Source)
    (edits : List (Name × List (Row Version Source))) (key : Name) :
    publish base edits key = (lookupEdit key edits).getD (base key) := by
  induction edits generalizing base with
  | nil => rfl
  | cons edit tail ih =>
    obtain ⟨name, rows⟩ := edit
    change publish (write base name rows) tail key = _
    rw [ih]
    cases found : lookupEdit key tail with
    | none =>
      by_cases same : key = name
      · subst name
        simp [lookupEdit, write, found]
      · simp [lookupEdit, write, found, same]
    | some bucket => simp [lookupEdit, found]

-- The native lock makes this decision and head replacement one operation.
-- A proposal carries its exact publication authority and snapshot identity.
structure Proposal (Name Version Source : Type) where
  owner : Nat
  base : Nat
  candidate : Catalog Name Version Source

def stage [DecidableEq Name] (owner base : Nat) (rows : Catalog Name Version Source)
    (edits : List (Name × List (Row Version Source))) : Proposal Name Version Source :=
  ⟨owner, base, publish rows edits⟩

def install (owner head : Nat) (proposal : Proposal Name Version Source) :
    Option (Catalog Name Version Source) :=
  if owner = proposal.owner ∧ head = proposal.base then some proposal.candidate else none

theorem install_staged_exact [DecidableEq Name] (owner base : Nat)
    (rows : Catalog Name Version Source) (edits : List (Name × List (Row Version Source))) :
    install owner base (stage owner base rows edits) = some (publish rows edits) := by
  simp [install, stage]

theorem foreign_even_with_shared_base_refused (owner : Nat)
    (proposal : Proposal Name Version Source) (foreign : owner ≠ proposal.owner) :
    install owner proposal.base proposal = none := by
  simp [install, foreign]

theorem changed_head_refused (head : Nat) (proposal : Proposal Name Version Source)
    (advanced : head ≠ proposal.base) : install proposal.owner head proposal = none := by
  simp [install, advanced]

-- A borrowed row handle has no authority in a staged publication. Read
-- each handle once when preparing the edited bucket and publish its values.
def capturedBucket (read : Nat → Row Version Source) (handles : List Nat) :
    List (Row Version Source) := handles.map read

theorem staged_bucket_uses_captured_rows [DecidableEq Name]
    (rows : Catalog Name Version Source) (owner base : Nat) (key : Name)
    (read : Nat → Row Version Source) (handles : List Nat) :
    (install owner base (stage owner base rows [(key, capturedBucket read handles)])).map
      (fun published => published key) = some (handles.map read) := by
  rw [install_staged_exact]
  change some (publish rows [(key, capturedBucket read handles)] key) = _
  rw [cold_equivalence]
  simp [lookupEdit, capturedBucket]

theorem borrowing_live_rows_can_change_a_staged_bucket
    (before after : Nat → Row Version Source) (handle : Nat)
    (changed : before handle ≠ after handle) :
    capturedBucket before [handle] ≠ capturedBucket after [handle] := by
  simpa [capturedBucket] using changed

def versions (base : Catalog Name Version Source) (key : Name) : List Version :=
  (base key).map Row.version

-- Resolution receives explicitly selected opaque version identities. Version
-- precedence and source installation are outside this Catalog contract.
inductive ResolutionError where | missing | conflict
  deriving DecidableEq

def choose [DecidableEq Version] (rows : List (Row Version Source))
    (version : Version) : Except ResolutionError (Row Version Source) :=
  match rows.filter (fun row => decide (row.version = version)) with
  | [] => .error .missing
  | [row] => .ok row
  | _ => .error .conflict

private abbrev VersionChoice (Version Source : Type) :=
  Except ResolutionError (Row Version Source)

private def addVersionChoice (prior : Option (VersionChoice Version Source))
    (row : Row Version Source) : VersionChoice Version Source :=
  if prior.isSome then .error .conflict else .ok row

private def putVersion [BEq Version] [Hashable Version]
    (index : Std.HashMap Version (VersionChoice Version Source)) (row : Row Version Source) :=
  index.insert row.version (addVersionChoice index[row.version]? row)

private theorem version_fold_reads_one_key [DecidableEq Version] [BEq Version]
    [LawfulBEq Version] [Hashable Version]
    (rows : List (Row Version Source)) (key : Version)
    (index : Std.HashMap Version (VersionChoice Version Source)) :
    (rows.foldl putVersion index)[key]? =
      (rows.filter (fun row => decide (row.version = key))).foldl
        (fun found row => some (addVersionChoice found row)) index[key]? := by
  induction rows generalizing index with
  | nil => rfl
  | cons row rest ih =>
    rw [List.foldl_cons, ih]
    by_cases same : row.version = key
    · simp [putVersion, same]
    · simp [putVersion, Std.HashMap.getElem?_insert, beq_iff_eq, same]

private theorem folded_conflict_stays_conflict (rows : List (Row Version Source)) :
    rows.foldl (fun found row => some (addVersionChoice found row)) (some (.error .conflict)) =
      some (.error .conflict) := by
  induction rows with
  | nil => rfl
  | cons row tail ih => simpa [List.foldl_cons, addVersionChoice] using ih

/-- A wide bucket can index one version entry per distinct identity. A second
row marks conflict even when its source is identical. The order of the
separately retained enumeration spine is never changed by the index. -/
theorem version_index_matches_choose [DecidableEq Version] [BEq Version] [LawfulBEq Version]
    [Hashable Version] (rows : List (Row Version Source)) (key : Version) :
    ((rows.foldl putVersion (∅ : Std.HashMap Version (VersionChoice Version Source)))[key]?).getD
      (.error .missing) = choose rows key := by
  rw [version_fold_reads_one_key]
  unfold choose
  cases rows.filter (fun row => decide (row.version = key)) with
  | nil => simp
  | cons row tail =>
    cases tail with
    | nil => simp [addVersionChoice]
    | cons another tail =>
      simp only [Std.HashMap.getElem?_empty, List.foldl_cons]
      change (tail.foldl (fun found row => some (addVersionChoice found row))
        (some (.error .conflict))).getD (.error .missing) = .error .conflict
      rw [folded_conflict_stays_conflict]
      rfl

private def replaceVersionSource [DecidableEq Version] (key : Version)
    (source : Source) (row : Row Version Source) : Row Version Source :=
  if row.version = key then {row with source := source} else row

private theorem replacement_keeps_version [DecidableEq Version] (key : Version)
    (source : Source) (row : Row Version Source) :
    (replaceVersionSource key source row).version = row.version := by
  unfold replaceVersionSource
  split <;> rfl

theorem replacement_keeps_enumeration [DecidableEq Version] (key : Version)
    (source : Source) (rows : List (Row Version Source)) :
    (rows.map (replaceVersionSource key source)).map Row.version = rows.map Row.version := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [replacement_keeps_version, ih]

private theorem replacement_filter [DecidableEq Version] (key query : Version)
    (source : Source) (rows : List (Row Version Source)) :
    (rows.map (replaceVersionSource key source)).filter (fun row => decide (row.version = query)) =
      (rows.filter (fun row => decide (row.version = query))).map (replaceVersionSource key source) := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
    by_cases selected : row.version = query <;> simp [replacement_keeps_version, selected, ih]

/-- An admitted unique version can replace only its indexed row and share
the whole ordered name bucket. The reference query uses a cold scan. -/
theorem version_point_replacement_matches_cold [DecidableEq Version]
    (rows : List (Row Version Source)) (key query : Version)
    (prior : Row Version Source) (source : Source)
    (unique : choose rows key = .ok prior) :
    choose (rows.map (replaceVersionSource key source)) query =
      if query = key then .ok ⟨key, source⟩ else choose rows query := by
  unfold choose at unique ⊢
  rw [replacement_filter]
  by_cases queried : query = key
  · subst query
    simp only [↓reduceIte]
    cases selected : rows.filter (fun row => decide (row.version = key)) with
    | nil => simp [selected] at unique
    | cons row tail =>
      cases tail with
      | nil =>
        have version := (List.mem_filter.mp (show row ∈ rows.filter
          (fun row => decide (row.version = key)) by simp [selected])).2
        simp [replaceVersionSource, of_decide_eq_true version]
      | cons duplicate tail => simp [selected] at unique
  · simp only [queried, ↓reduceIte]
    have unchanged : ∀ row ∈ rows.filter (fun row => decide (row.version = query)),
        replaceVersionSource key source row = row := by
      intro row found
      have version := of_decide_eq_true (List.mem_filter.mp found).2
      simp [replaceVersionSource, version, queried]
    rw [List.map_congr_left (g := id) unchanged, List.map_id]

theorem version_point_index_patch_exact [DecidableEq Version] [BEq Version] [LawfulBEq Version]
    [Hashable Version] (rows : List (Row Version Source)) (key query : Version)
    (prior : Row Version Source) (source : Source) (unique : choose rows key = .ok prior) :
    let index := rows.foldl putVersion (∅ : Std.HashMap Version (VersionChoice Version Source))
    ((index.insert key (.ok ⟨key, source⟩))[query]?).getD (.error .missing) =
      choose (rows.map (replaceVersionSource key source)) query := by
  dsimp only
  rw [version_point_replacement_matches_cold rows key query prior source unique]
  by_cases queried : query = key
  · simp [queried]
  · have other : key ≠ query := fun same => queried same.symm
    simp [Std.HashMap.getElem?_insert, beq_iff_eq, other, queried, version_index_matches_choose]

def demand [DecidableEq Version] (rows : List (Row Version Source)) (version : Version)
    (read : Source → Dependency) : Except ResolutionError Dependency × List Source :=
  match choose rows version with
  | .error reason => (.error reason, [])
  | .ok row => (.ok (read row.source), [row.source])

theorem refusal_reads_nothing [DecidableEq Version] (rows : List (Row Version Source))
    (version : Version) (read : Source → Dependency) (reason : ResolutionError)
    (refused : choose rows version = .error reason) :
    demand rows version read = (.error reason, []) := by simp [demand, refused]

theorem selection_reads_exact_source [DecidableEq Version] (rows : List (Row Version Source))
    (version : Version) (read : Source → Dependency) (row : Row Version Source)
    (chosen : choose rows version = .ok row) :
    demand rows version read = (.ok (read row.source), [row.source]) := by simp [demand, chosen]

theorem conflicting_identity_refuses [DecidableEq Version] (version : Version) (first second : Source) :
    choose [⟨version, first⟩, ⟨version, second⟩] version = .error .conflict := by simp [choose]

abbrev Pins (Name Version : Type) := Name → Option Version

def addPin [DecidableEq Name] [DecidableEq Version] (pins : Pins Name Version)
    (req : Name × Version) : Option (Pins Name Version) :=
  match pins req.1 with
  | none => some (fun k => if k = req.1 then some req.2 else pins k)
  | some v => if v = req.2 then some pins else none

def collectPins [DecidableEq Name] [DecidableEq Version] (pins : Pins Name Version) :
    List (Name × Version) → Option (Pins Name Version)
  | [] => some pins
  | req :: rest => (addPin pins req).bind (fun next => collectPins next rest)

def Extends (next prior : Pins Name Version) : Prop :=
  ∀ name version, prior name = some version → next name = some version

theorem addPin_sound [DecidableEq Name] [DecidableEq Version] (pins next : Pins Name Version)
    (req : Name × Version) (accepted : addPin pins req = some next) :
    Extends next pins ∧ next req.1 = some req.2 := by
  unfold addPin at accepted
  cases known : pins req.1 with
  | none =>
    simp only [known, Option.some.injEq] at accepted
    subst next
    refine ⟨?_, by simp⟩
    intro name version before
    by_cases same : name = req.1
    · subst name
      simp [known] at before
    · simp [same, before]
  | some v =>
    by_cases same : v = req.2
    · simp [known, same] at accepted
      subst next
      exact ⟨fun _ _ e => e, known.trans (congrArg some same)⟩
    · simp [known, same] at accepted

theorem collectPins_sound [DecidableEq Name] [DecidableEq Version] (pins final : Pins Name Version)
    (requests : List (Name × Version)) (accepted : collectPins pins requests = some final) :
    Extends final pins ∧ ∀ req ∈ requests, final req.1 = some req.2 := by
  induction requests generalizing pins with
  | nil =>
    simp [collectPins] at accepted
    subst final
    exact ⟨fun _ _ e => e, by simp⟩
  | cons req rest ih =>
    unfold collectPins at accepted
    cases first : addPin pins req with
    | none => simp [first] at accepted
    | some staged =>
      have ⟨preserved, inserted⟩ := addPin_sound pins staged req first
      have ⟨tail, agrees⟩ := ih staged (by simpa [first] using accepted)
      refine ⟨fun k v h => tail k v (preserved k v h), ?_⟩
      intro constraint member
      rcases List.mem_cons.mp member with equal | remainder
      · subst constraint
        exact tail _ _ inserted
      · exact agrees _ remainder

theorem conflicting_requirements_refused [DecidableEq Name] [DecidableEq Version]
    (pins : Pins Name Version) (requests : List (Name × Version)) (name : Name)
    (first second : Version) (distinct : first ≠ second)
    (a : (name, first) ∈ requests) (b : (name, second) ∈ requests) :
    collectPins pins requests = none := by
  cases outcome : collectPins pins requests with
  | none => rfl
  | some final =>
    have agrees := (collectPins_sound pins final requests outcome).2
    exact False.elim (distinct (Option.some.inj ((agrees _ a).symm.trans (agrees _ b))))

-- Demand receives only a completed pure plan, which may also fail on a late
-- missing or ambiguous catalog row after pins were collected successfully.
def demandPlan (selected : Except ResolutionError (List Source)) (read : Source → Dependency) :
    Except ResolutionError (List Dependency) × List Source :=
  match selected with
  | .ok rows => (.ok (rows.map read), rows)
  | .error failure => (.error failure, [])

theorem rejected_plan_has_no_reads (reason : ResolutionError) (read : Source → Dependency) :
    demandPlan (.error reason) read = (.error reason, []) := rfl

#print axioms conflicting_requirements_refused
#print axioms rejected_plan_has_no_reads

end ModuleCatalog
