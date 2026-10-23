import LeanPoo.Functional.TableStyle

/-! Key-preserving bulk maps over one original admitted snapshot. Callback errors
and whole-root refusals are private until the existing style commit. Backend
lookup/traversal laws are premises; this does not verify Gerbil tree compilation,
callback termination, physical allocation or garbage collection. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Inspect each original binding once, in order; optional output only changes its
value or removes it. A callback never receives a newly staged binding. -/
def mapBindings (transform : K → V → Except E (Option V)) :
    List (K × V) → Except E (List (K × V))
  | [] => .ok []
  | (key, value) :: rest =>
    match transform key value with
    | .error cause => .error cause
    | .ok next => match mapBindings transform rest with
      | .error cause => .error cause
      | .ok mapped => .ok (match next with | none => mapped | some v => (key, v) :: mapped)

/-- A pure optional mapper agrees exactly with the standard stable filterMap. -/
theorem mapBindings_total (transform : K → V → Option V) (rows : List (K × V)) :
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
theorem mapBindings_length (transform : K → V → Except E (Option V))
    (rows mapped : List (K × V)) (success : mapBindings transform rows = .ok mapped) :
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
theorem mapBindings_keys (transform : K → V → Except E (Option V))
    (rows mapped : List (K × V)) (success : mapBindings transform rows = .ok mapped)
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
theorem mapBindings_transport (key : K → L) (value : V → W)
    (source : K → V → Except E (Option V)) (target : L → W → Except E (Option W))
    (aligned : ∀ k v, target (key k) (value v) =
      match source k v with
      | .error cause => .error cause
      | .ok next => .ok (next.map value)) (rows : List (K × V)) :
    mapBindings target (rows.map (fun row => (key row.1, value row.2))) =
      match mapBindings source rows with
      | .error cause => .error cause
      | .ok mapped => .ok (mapped.map (fun row => (key row.1, value row.2))) := by
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
def prepareBindingMap (transform : K → V → Except E (Option V))
    (admit : List (K × V) → Except E Unit) (rows : List (K × V)) : Except E (List (K × V)) :=
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

end LeanPoo.Functional.OrderedDictionary
