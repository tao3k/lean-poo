import LeanPoo.Functional.TableStyle

/-! Key-preserving bulk maps over one original admitted snapshot. Callback errors
and whole-root refusals are private until the existing style commit. Backend
lookup/traversal laws are premises; this does not verify Gerbil tree compilation,
callback termination, physical allocation or garbage collection. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Inspect each original binding once, in order; optional output only changes its
value or removes it. A callback never receives a newly staged binding. -/
def mapBindings (transform : K → V → Except E (Option W)) :
    List (K × V) → Except E (List (K × W))
  | [] => .ok []
  | (key, value) :: rest =>
    match transform key value with
    | .error cause => .error cause
    | .ok next => match mapBindings transform rest with
      | .error cause => .error cause
      | .ok mapped => .ok (match next with | none => mapped | some v => (key, v) :: mapped)

/-- A pure optional mapper agrees exactly with the standard stable filterMap. -/
theorem mapBindings_total (transform : K → V → Option W) (rows : List (K × V)) :
    mapBindings (E := E) (fun key value => .ok (transform key value)) rows =
      .ok (rows.filterMap (fun row => (transform row.1 row.2).map (row.1, ·))) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases h : transform key value <;> simp [mapBindings, ih, h]

/-- Required maps preserve the exact key sequence and callback-produced values. -/
theorem mapBindings_required (transform : K → V → V) (rows : List (K × V)) :
    mapBindings (E := E) (fun key value => .ok (some (transform key value))) rows =
      .ok (rows.map (fun row => (row.1, transform row.1 row.2))) := by
  induction rows with
  | nil => rfl
  | cons head tail ih => cases head; simp [mapBindings, ih]

/-- Identity mapping retains opaque payloads without requiring value equality. -/
theorem mapBindings_identity (rows : List (K × V)) :
    mapBindings (E := E) (fun _ value => .ok (some value)) rows = .ok rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih => cases head; simp [mapBindings, ih]

/-- Dropping original bindings can never grow the domain or add a binding. -/
theorem mapBindings_length (transform : K → V → Except E (Option W))
    (rows : List (K × V)) (mapped : List (K × W)) (success : mapBindings transform rows = .ok mapped) :
    mapped.length ≤ rows.length := by
  induction rows generalizing mapped with
  | nil => simp [mapBindings] at success; subst mapped; simp
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases hc : transform key value with
    | error cause => simp [mapBindings, hc] at success
    | ok next =>
      cases ht : mapBindings transform tail with
      | error cause => simp [mapBindings, hc, ht] at success
      | ok rest =>
        have bound := ih rest ht
        cases next <;> simp [mapBindings, hc, ht] at success <;> subst mapped <;>
          simp only [List.length_cons] <;> omega

/-- Every successful output key comes from the original snapshot. -/
theorem mapBindings_keys (transform : K → V → Except E (Option W))
    (rows : List (K × V)) (mapped : List (K × W)) (success : mapBindings transform rows = .ok mapped)
    (query : K) (present : query ∈ mapped.map Prod.fst) : query ∈ rows.map Prod.fst := by
  induction rows generalizing mapped with
  | nil => simp [mapBindings] at success; subst mapped; simp at present
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases hc : transform key value with
    | error cause => simp [mapBindings, hc] at success
    | ok next =>
      cases ht : mapBindings transform tail with
      | error cause => simp [mapBindings, hc, ht] at success
      | ok rest =>
        cases next with
        | none =>
          simp [mapBindings, hc, ht] at success
          subst mapped
          exact List.mem_cons_of_mem key (ih rest ht present)
        | some v =>
          simp [mapBindings, hc, ht] at success
          subst mapped
          simp only [List.map_cons, List.mem_cons] at present ⊢
          rcases present with same | later
          · exact .inl same
          · exact .inr (ih rest ht later)

/-- A declared representation transfers mapping when its visible callback agrees
with translating the source result. Inverse/shape laws belong to the existing
Wrapper; no point-by-point installation or intermediate index state is assumed. -/
theorem mapBindings_transport (key : K → L) (input : V → W) (output : X → Y)
    (source : K → V → Except E (Option X)) (target : L → W → Except E (Option Y))
    (aligned : ∀ k v, target (key k) (input v) =
      match source k v with
      | .error cause => .error cause
      | .ok next => .ok (next.map output)) (rows : List (K × V)) :
    mapBindings target (rows.map (fun row => (key row.1, input row.2))) =
      match mapBindings source rows with
      | .error cause => .error cause
      | .ok mapped => .ok (mapped.map (fun row => (key row.1, output row.2))) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨k, v⟩
    cases hs : source k v with
    | error cause => simp [mapBindings, aligned, hs]
    | ok next =>
      cases ht : mapBindings source tail with
      | error cause => simp [mapBindings, aligned, hs, ih, ht]
      | ok rest => cases next <;> simp [mapBindings, aligned, hs, ih, ht]

/-- Complete root recognition can refuse but cannot rewrite admitted leaves. -/
def prepareBindingMap (transform : K → V → Except E (Option W))
    (admit : List (K × W) → Except E Unit) (rows : List (K × V)) : Except E (List (K × W)) :=
  match mapBindings transform rows with
  | .error cause => .error cause
  | .ok mapped => match admit mapped with
    | .error cause => .error cause
    | .ok () => .ok mapped

/-- All styles reuse the original single-result owner transaction. -/
def styleMapBindings (style : TableStyle) (state : Option (List (K × V)))
    (transform : K → V → Except E (Option V)) (admit : List (K × V) → Except E Unit) :=
  styleStep style state (prepareBindingMap transform admit)

/-- A late callback failure preserves the original owner and exact failure. -/
theorem styleMapBindings_refused (style : TableStyle) (rows : List (K × V))
    (transform : K → V → Except E (Option V)) (admit : List (K × V) → Except E Unit)
    (cause : E) (refused : mapBindings transform rows = .error cause) :
    styleMapBindings style (some rows) transform admit = (some rows, .error (.callback cause)) := by
  apply styleStep_failure
  simp [prepareBindingMap, refused]

/-- A whole-table refinement failure also precedes the only owner installation. -/
theorem styleMapBindings_root_refused (style : TableStyle) (rows mapped : List (K × V))
    (transform : K → V → Except E (Option V)) (admit : List (K × V) → Except E Unit)
    (cause : E) (ready : mapBindings transform rows = .ok mapped)
    (refused : admit mapped = .error cause) :
    styleMapBindings style (some rows) transform admit = (some rows, .error (.callback cause)) := by
  apply styleStep_failure
  simp [prepareBindingMap, ready, refused]

/-- A retired input cannot invoke any binding callback. -/
theorem styleMapBindings_consumed (style : TableStyle)
    (transform : K → V → Except E (Option V)) (admit : List (K × V) → Except E Unit) :
    styleMapBindings style none transform admit = (none, .error .consumed) := rfl

/-- Even an observational identity map retires a linear predecessor. -/
theorem styleMapBindings_identity_linear (rows : List (K × V)) :
    styleMapBindings (E := E) .linear (some rows) (fun _ v => .ok (some v)) (fun _ => .ok ()) =
      (none, .ok rows) := by
  simp [styleMapBindings, prepareBindingMap, mapBindings_identity, styleStep]

/-- Generic primary installation writes once per changed decision; specialized tree
rebuilds, secondary-index work and conversions have separate costs; this is not
a bound on total backend writes, allocation or nodes. -/
def mappingWrites : List Bool → Nat
  | [] => 0
  | changed :: rest => (if changed then 1 else 0) + mappingWrites rest

/-- With one change decision per visited binding, writes never exceed callbacks. -/
theorem mappingWrites_bound (decisions : List Bool) : mappingWrites decisions ≤ decisions.length := by
  induction decisions with
  | nil => simp [mappingWrites]
  | cons changed rest ih => cases changed <;> simp [mappingWrites] <;> omega

/-- Reentrant/competing work prepared from an older head cannot overwrite a winner. -/
theorem installBindingMap_stale (style : TableStyle) (current : TableGeneration A)
    (expected : Nat) (mapped : A) (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected mapped = (current, .error .stale) :=
  installStyle_stale style current expected mapped stale

/-- The backend supplies a finite, nonrepeating union-domain order. Each request
reads both ORIGINAL views; no staged output is used to prepare a later request. -/
def mergeRequests (keys : List K) (left right : K → Option V) :
    List (K × (Option V × Option V)) := keys.map (fun key => (key, left key, right key))

/-- Exactly one resolver opportunity is prepared for each supplied domain key. -/
theorem mergeRequests_keys (keys : List K) (left right : K → Option V) :
    (mergeRequests keys left right).map Prod.fst = keys := by
  simp [mergeRequests, List.map_map, Function.comp_def]

/-- Binary combination reuses the same effectful map traversal with a request
payload type distinct from its output value type. Failure order is unchanged. -/
def mergeBindings (choose : K → Option V → Option V → Except E (Option V))
    (requests : List (K × (Option V × Option V))) : Except E (List (K × V)) :=
  mapBindings (fun key pair => choose key pair.1 pair.2) requests

/-- A total resolver agrees with stable filtering of the supplied domain order. -/
theorem mergeBindings_total (choose : K → Option V → Option V → Option V)
    (requests : List (K × (Option V × Option V))) :
    mergeBindings (E := E) (fun k a b => .ok (choose k a b)) requests =
      .ok (requests.filterMap (fun row => (choose row.1 row.2.1 row.2.2).map (row.1, ·))) :=
  mapBindings_total _ _

/-- No resolver can invent a key absent from the backend's declared domain. -/
theorem mergeBindings_keys (choose : K → Option V → Option V → Except E (Option V))
    (keys : List K) (left right : K → Option V) (result : List (K × V))
    (ready : mergeBindings choose (mergeRequests keys left right) = .ok result)
    (key : K) (present : key ∈ result.map Prod.fst) : key ∈ keys := by
  have h := mapBindings_keys (fun k (pair : Option V × Option V) => choose k pair.1 pair.2)
    (mergeRequests keys left right) result ready key present
  simpa only [mergeRequests_keys] using h

/-- A union invokes its resolver only where BOTH snapshots have a binding.
Missing is distinct from some false; a one-sided value is preserved verbatim. -/
def unionDecision (choose : K → V → V → Except E (Option V)) (key : K)
    (left right : Option V) : Except E (Option V) :=
  match left, right with
  | some a, some b => choose key a b
  | some a, none => .ok (some a)
  | none, other => .ok other

/-- A right-only binding never invokes an overlap callback, even one that fails. -/
theorem unionDecision_right_only (choose : K → V → V → Except E (Option V))
    (key : K) (value : V) : unionDecision choose key none (some value) = .ok (some value) := rfl

/-- A left-only binding similarly retains its already admitted opaque value. -/
theorem unionDecision_left_only (choose : K → V → V → Except E (Option V))
    (key : K) (value : V) : unionDecision choose key (some value) none = .ok (some value) := rfl

/-- The complete output is recognized before the existing owner step installs it.
Index uniqueness and representation laws are premises of the backend installer. -/
def prepareBindingMerge (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) (requests : List (K × (Option V × Option V))) :=
  prepareBindingMap (fun key pair => choose key pair.1 pair.2) admit requests

/-- Only the left capability is state. The request builder captures the right
persistent snapshot, with backend-specific order and lookup laws kept explicit. -/
def styleMergeBindings (style : TableStyle) (state : Option (List (K × V)))
    (requests : List (K × V) → List (K × (Option V × Option V)))
    (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) :=
  styleStep style state (fun before => prepareBindingMerge choose admit (requests before))

/-- The first resolver failure exposes no partial output or changed owner. -/
theorem styleMergeBindings_refused (style : TableStyle) (before : List (K × V))
    (requests : List (K × V) → List (K × (Option V × Option V)))
    (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) (cause : E)
    (refused : mergeBindings choose (requests before) = .error cause) :
    styleMergeBindings style (some before) requests choose admit =
      (some before, .error (.callback cause)) := by
  apply styleStep_failure
  simp [prepareBindingMerge, prepareBindingMap, mergeBindings] at refused ⊢
  simp [refused]

/-- Index/refinement refusal follows private merging and still retains the owner. -/
theorem styleMergeBindings_root_refused (style : TableStyle) (before result : List (K × V))
    (requests : List (K × V) → List (K × (Option V × Option V)))
    (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) (cause : E)
    (ready : mergeBindings choose (requests before) = .ok result)
    (refused : admit result = .error cause) :
    styleMergeBindings style (some before) requests choose admit =
      (some before, .error (.callback cause)) := by
  apply styleStep_failure
  simp [mergeBindings] at ready
  simp [prepareBindingMerge, prepareBindingMap, ready, refused]

/-- A consumed predecessor cannot invoke the request builder or resolver. -/
theorem styleMergeBindings_consumed (style : TableStyle)
    (requests : List (K × V) → List (K × (Option V × Option V)))
    (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) :
    styleMergeBindings style none requests choose admit = (none, .error .consumed) := rfl

/-- Successful linear merging consumes only its left predecessor once. -/
theorem styleMergeBindings_linear (before result : List (K × V))
    (requests : List (K × V) → List (K × (Option V × Option V)))
    (choose : K → Option V → Option V → Except E (Option V))
    (admit : List (K × V) → Except E Unit)
    (ready : prepareBindingMerge choose admit (requests before) = .ok result) :
    styleMergeBindings .linear (some before) requests choose admit = (none, .ok result) := by
  simp [styleMergeBindings, styleStep, ready]

/-- Explicit key/value representation changes conjugate BOTH optional inputs and
all results through the existing mapping transport law. Ordering is supplied by
aligned backend requests, never inferred from host key order. -/
theorem mergeBindings_transport (key : K → L) (value : V → W)
    (source : K → Option V → Option V → Except E (Option V))
    (target : L → Option W → Option W → Except E (Option W))
    (aligned : ∀ k a b, target (key k) (a.map value) (b.map value) =
      match source k a b with
      | .error cause => .error cause
      | .ok next => .ok (next.map value))
    (requests : List (K × (Option V × Option V))) :
    mergeBindings target (requests.map (fun row =>
      (key row.1, row.2.1.map value, row.2.2.map value))) =
      match mergeBindings source requests with
      | .error cause => .error cause
      | .ok merged => .ok (merged.map (fun row => (key row.1, value row.2))) := by
  apply mapBindings_transport key (fun pair => (pair.1.map value, pair.2.map value)) value
    (fun k pair => source k pair.1 pair.2) (fun k pair => target k pair.1 pair.2)
    (fun k pair => aligned k pair.1 pair.2) requests

/-- Left-biased presence never treats a stored false as missing. -/
def leftJoinOption (left right : Option V) : Option V :=
  match left with | some value => some value | none => right

/-- Regrouping accepted joins cannot change operand priority or opaque values. -/
theorem leftJoinOption_assoc (a b c : Option V) :
    leftJoinOption (leftJoinOption a b) c = leftJoinOption a (leftJoinOption b c) := by
  cases a <;> rfl

/-- Complete binary joining is the same stable resolver used by merging. -/
theorem mergeBindings_join (requests : List (K × (Option V × Option V))) :
    mergeBindings (E := E) (fun _ a b => .ok (leftJoinOption a b)) requests =
      .ok (requests.filterMap (fun row => (leftJoinOption row.2.1 row.2.2).map (row.1, ·))) :=
  mergeBindings_total _ _

/-- Output size is bounded by the supplied union domain, excluding backend index,
representation, preparation and admission work from this structural statement. -/
theorem mergeBindings_length (choose : K → Option V → Option V → Except E (Option V))
    (keys : List K) (left right : K → Option V) (result : List (K × V))
    (ready : mergeBindings choose (mergeRequests keys left right) = .ok result) :
    result.length ≤ keys.length := by
  have h := mapBindings_length (fun k (pair : Option V × Option V) => choose k pair.1 pair.2)
    (mergeRequests keys left right) result ready
  simpa [mergeRequests] using h

/-- If the supplied domain contains only live keys, the merged result cannot
introduce any binding absent from BOTH original snapshots. -/
theorem mergeBindings_domain (choose : K → Option V → Option V → Except E (Option V))
    (keys : List K) (left right : K → Option V) (result : List (K × V))
    (domain : ∀ k ∈ keys, (left k).isSome ∨ (right k).isSome)
    (ready : mergeBindings choose (mergeRequests keys left right) = .ok result)
    (key : K) (present : key ∈ result.map Prod.fst) :
    (left key).isSome ∨ (right key).isSome :=
  domain key (mergeBindings_keys choose keys left right result ready key present)

/-- Generic equality is a read relation: matching left values and right-domain
inclusion. It never constructs an empty root or asks it to satisfy a refinement. -/
def bindingViewsEqual (same : V → V → Bool) (leftKeys rightKeys : List K)
    (left right : K → Option V) : Bool :=
  leftKeys.all (fun key => match left key, right key with
    | some a, some b => same a b
    | _, _ => false) && rightKeys.all (fun key => (left key).isSome)

/-- Reflexive value equality and a live finite enumeration suffice for equality;
no neutral table root, value normalization or Function equality decision is used. -/
theorem bindingViewsEqual_refl (same : V → V → Bool) (keys : List K) (view : K → Option V)
    (reflexive : ∀ value, same value value = true)
    (live : ∀ key ∈ keys, (view key).isSome = true) :
    bindingViewsEqual same keys keys view view = true := by
  simp only [bindingViewsEqual, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro key member
    cases h : view key with
    | none => have impossible := live key member; simp [h] at impossible
    | some value => simp [reflexive]
  · exact live

/-- Under complete backend enumerations and a sound child equality, successful
read comparison means identical optional observations at every logical key. -/
theorem bindingViewsEqual_sound (same : V → V → Bool) (leftKeys rightKeys : List K)
    (left right : K → Option V)
    (child : ∀ a b, same a b = true → a = b)
    (leftComplete : ∀ key value, left key = some value → key ∈ leftKeys)
    (rightComplete : ∀ key value, right key = some value → key ∈ rightKeys)
    (ready : bindingViewsEqual same leftKeys rightKeys left right = true) : left = right := by
  simp only [bindingViewsEqual, Bool.and_eq_true, List.all_eq_true] at ready
  obtain ⟨allMatching, includes⟩ := ready
  funext key
  cases hl : left key with
  | none =>
    cases hr : right key with
    | none => rfl
    | some value =>
      have impossible := includes key (rightComplete key value hr)
      simp [hl] at impossible
  | some a =>
    have observed := allMatching key (leftComplete key a hl)
    cases hr : right key with
    | none => simp [hl, hr] at observed
    | some b =>
      have equal := child a b (by simpa [hl, hr] using observed)
      simp [equal]

/-- Ordered heterogeneous entry projection with a private target-key registry.
Keys denote the backend's logical equality classes. Callback refusal and the
first duplicate are distinct; neither produces a partial output. -/
def mapEntries [DecidableEq L] (transform : K → V → Except E (Option (L × W))) :
    List (K × V) → List L → Except (E ⊕ L) (List (L × W))
  | [], _ => .ok []
  | (key, value) :: rest, seen =>
    match transform key value with
    | .error cause => .error (.inl cause)
    | .ok none => mapEntries transform rest seen
    | .ok (some row) =>
      if row.1 ∈ seen then .error (.inr row.1)
      else (mapEntries transform rest (row.1 :: seen)).map (row :: ·)

/-- A callback refusal precedes every later projection or target construction. -/
theorem mapEntries_callback_refused [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (key : K) (value : V)
    (rest : List (K × V)) (seen : List L) (cause : E)
    (refused : transform key value = .error cause) :
    mapEntries transform ((key, value) :: rest) seen = .error (.inl cause) := by
  simp [mapEntries, refused]

/-- Even equal payloads cannot silently overwrite an earlier projected key. -/
theorem mapEntries_collision [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (key : K) (value : V)
    (rest : List (K × V)) (seen : List L) (row : L × W)
    (projected : transform key value = .ok (some row)) (duplicate : row.1 ∈ seen) :
    mapEntries transform ((key, value) :: rest) seen = .error (.inr row.1) := by
  simp [mapEntries, projected, duplicate]

/-- Successful optional projection emits at most one binding per source row. -/
theorem mapEntries_length [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (rows : List (K × V))
    (seen : List L) (mapped : List (L × W))
    (success : mapEntries transform rows seen = .ok mapped) : mapped.length ≤ rows.length := by
  induction rows generalizing seen mapped with
  | nil => simp [mapEntries] at success; subst mapped; simp
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases hc : transform key value with
    | error cause => simp [mapEntries, hc] at success
    | ok next =>
      cases next with
      | none => exact Nat.le_trans (ih seen mapped (by simpa [mapEntries, hc] using success)) (by simp)
      | some row =>
        by_cases duplicate : row.1 ∈ seen
        · simp [mapEntries, hc, duplicate] at success
        · cases ht : mapEntries transform tail (row.1 :: seen) with
          | error cause => simp [mapEntries, hc, duplicate, ht, Except.map] at success
          | ok rest =>
            simp [mapEntries, hc, duplicate, ht, Except.map] at success
            subst mapped
            have bound := ih (row.1 :: seen) rest ht
            simp only [List.length_cons]
            omega

/-- The private registry excludes every previously accepted target key. -/
theorem mapEntries_avoids [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (rows : List (K × V))
    (seen : List L) (mapped : List (L × W))
    (success : mapEntries transform rows seen = .ok mapped) :
    ∀ key ∈ mapped.map Prod.fst, key ∉ seen := by
  induction rows generalizing seen mapped with
  | nil => simp [mapEntries] at success; subst mapped; simp
  | cons head tail ih =>
    rcases head with ⟨source, value⟩
    cases hc : transform source value with
    | error cause => simp [mapEntries, hc] at success
    | ok next =>
      cases next with
      | none => exact ih seen mapped (by simpa [mapEntries, hc] using success)
      | some row =>
        by_cases duplicate : row.1 ∈ seen
        · simp [mapEntries, hc, duplicate] at success
        · cases ht : mapEntries transform tail (row.1 :: seen) with
          | error cause => simp [mapEntries, hc, duplicate, ht, Except.map] at success
          | ok rest =>
            simp [mapEntries, hc, duplicate, ht, Except.map] at success
            subst mapped
            intro key present
            simp only [List.map_cons, List.mem_cons] at present
            rcases present with same | later
            · subst key; exact duplicate
            · exact fun h => ih (row.1 :: seen) rest ht key later (List.mem_cons_of_mem _ h)

/-- A published entry sequence has no duplicate logical target keys. -/
theorem mapEntries_nodup [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (rows : List (K × V))
    (seen : List L) (mapped : List (L × W))
    (success : mapEntries transform rows seen = .ok mapped) : (mapped.map Prod.fst).Nodup := by
  induction rows generalizing seen mapped with
  | nil => simp [mapEntries] at success; subst mapped; simp
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases hc : transform key value with
    | error cause => simp [mapEntries, hc] at success
    | ok next =>
      cases next with
      | none => exact ih seen mapped (by simpa [mapEntries, hc] using success)
      | some row =>
        by_cases duplicate : row.1 ∈ seen
        · simp [mapEntries, hc, duplicate] at success
        · cases ht : mapEntries transform tail (row.1 :: seen) with
          | error cause => simp [mapEntries, hc, duplicate, ht, Except.map] at success
          | ok rest =>
            simp [mapEntries, hc, duplicate, ht, Except.map] at success
            subst mapped
            apply List.nodup_cons.mpr
            constructor
            · exact fun h => mapEntries_avoids transform tail (row.1 :: seen) rest ht row.1 h (by simp)
            · exact ih (row.1 :: seen) rest ht

/-- Source admission, finite projection, one complete constructor and final
recognition share one Except pipeline. No empty/intermediate target is required. -/
def prepareEntryMap [DecidableEq L] (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) : Except (E ⊕ L) A :=
  ((admitSource rows).mapError Sum.inl).bind fun _ =>
    (mapEntries transform rows []).bind fun mapped =>
      ((construct mapped).mapError Sum.inl).bind fun root =>
        ((admitTarget root).mapError Sum.inl).map fun _ => root

/-- An invalid source suppresses projections and target preparation. -/
theorem prepareEntryMap_source_refused [DecidableEq L]
    (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) (cause : E) (refused : admitSource rows = .error cause) :
    prepareEntryMap transform admitSource construct admitTarget rows = .error (.inl cause) := by
  simp [prepareEntryMap, refused, Except.mapError, Except.bind]

/-- Projection/collision refusal never calls the complete target constructor. -/
theorem prepareEntryMap_projection_refused [DecidableEq L]
    (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) (cause : E ⊕ L) (accepted : admitSource rows = .ok ())
    (refused : mapEntries transform rows [] = .error cause) :
    prepareEntryMap transform admitSource construct admitTarget rows = .error cause := by
  simp [prepareEntryMap, accepted, refused, Except.mapError, Except.bind]

/-- Whole-target refusal cannot publish an unchecked constructor result. -/
theorem prepareEntryMap_target_refused [DecidableEq L]
    (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) (mapped : List (L × W)) (root : A) (cause : E)
    (accepted : admitSource rows = .ok ()) (projected : mapEntries transform rows [] = .ok mapped)
    (built : construct mapped = .ok root) (refused : admitTarget root = .error cause) :
    prepareEntryMap transform admitSource construct admitTarget rows = .error (.inl cause) := by
  simp [prepareEntryMap, accepted, projected, built, refused, Except.mapError, Except.bind, Except.map]

/-- Successful projection agrees with the existing ordered binding traversal,
then forgets only source keys. No equality or normalization of payloads is used. -/
theorem mapEntries_agrees [DecidableEq L]
    (transform : K → V → Except E (Option (L × W))) (rows : List (K × V))
    (seen : List L) (mapped : List (L × W))
    (success : mapEntries transform rows seen = .ok mapped) :
    (mapBindings transform rows).map (List.map Prod.snd) = .ok mapped := by
  induction rows generalizing seen mapped with
  | nil => simp [mapEntries] at success; subst mapped; rfl
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases hc : transform key value with
    | error cause => simp [mapEntries, hc] at success
    | ok next =>
      cases next with
      | none =>
        have ready := ih seen mapped (by simpa [mapEntries, hc] using success)
        cases hb : mapBindings transform tail <;> simp [hb, Except.map] at ready
        simp_all [mapBindings, Except.map]
      | some row =>
        by_cases duplicate : row.1 ∈ seen
        · simp [mapEntries, hc, duplicate] at success
        · cases ht : mapEntries transform tail (row.1 :: seen) with
          | error cause => simp [mapEntries, hc, duplicate, ht, Except.map] at success
          | ok rest =>
            simp [mapEntries, hc, duplicate, ht, Except.map] at success
            subst mapped
            have ready := ih (row.1 :: seen) rest ht
            cases hb : mapBindings transform tail <;> simp [hb, Except.map] at ready
            simp_all [mapBindings, Except.map]

/-- A successful complete constructor publishes its exact admitted root, without
requiring any private prefix to satisfy target business constraints. -/
theorem prepareEntryMap_ready [DecidableEq L]
    (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) (mapped : List (L × W)) (root : A)
    (accepted : admitSource rows = .ok ()) (projected : mapEntries transform rows [] = .ok mapped)
    (built : construct mapped = .ok root) (checked : admitTarget root = .ok ()) :
    prepareEntryMap transform admitSource construct admitTarget rows = .ok root := by
  simp [prepareEntryMap, accepted, projected, built, checked, Except.mapError, Except.bind, Except.map]

/-- Every published target satisfies a faithful whole-root recognizer. The
concrete carrier, key-equivalence registry and constructor laws remain premises. -/
theorem prepareEntryMap_valid [DecidableEq L]
    (transform : K → V → Except E (Option (L × W)))
    (admitSource : List (K × V) → Except E Unit)
    (construct : List (L × W) → Except E A) (admitTarget : A → Except E Unit)
    (rows : List (K × V)) (Valid : A → Prop)
    (faithful : ∀ root, admitTarget root = .ok () → Valid root) (root : A)
    (published : prepareEntryMap transform admitSource construct admitTarget rows = .ok root) : Valid root := by
  cases hs : admitSource rows with
  | error cause => simp [prepareEntryMap, hs, Except.mapError, Except.bind] at published
  | ok accepted =>
    cases hp : mapEntries transform rows [] with
    | error cause => simp [prepareEntryMap, hs, hp, Except.mapError, Except.bind] at published
    | ok mapped =>
      cases hb : construct mapped with
      | error cause => simp [prepareEntryMap, hs, hp, hb, Except.mapError, Except.bind] at published
      | ok output =>
        cases ha : admitTarget output with
        | error cause => simp [prepareEntryMap, hs, hp, hb, ha, Except.mapError, Except.bind, Except.map] at published
        | ok checked =>
          cases accepted; cases checked
          have same : output = root := by
            simpa [prepareEntryMap, hs, hp, hb, ha, Except.mapError, Except.bind, Except.map] using published
          subst root
          exact faithful output ha

end LeanPoo.Functional.OrderedDictionary
