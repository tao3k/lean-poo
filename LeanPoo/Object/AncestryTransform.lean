import LeanPoo.Object.Memo

/-! Chapter 9's non-modular wrapping of the current ancestry. This is an
explicit snapshot transformation; later ancestors and descendants do not
automatically participate in the wrapping protocol. -/

namespace LeanPoo.Object

universe u v w

/-- Transform one dependent entry without changing its key or equality
witness. The payload transformation receives that entry's actual key. -/
def Entry.mapPayload {Key : Type u} {Payload : Key → Type v}
    {Result : Key → Type w}
    (change : (key : Key) → Payload key → Result key)
    (entry : Entry Key Payload) : Entry Key Result :=
  ⟨entry.key, change entry.key entry.value, entry.decideEq⟩

/-- Mapping payloads commutes with last-direct-write lookup, including
repeated keys and heterogeneous payload types. -/
theorem Entry.lookup_mapPayload {Key : Type u} {Payload : Key → Type v}
    {Result : Key → Type w}
    (change : (key : Key) → Payload key → Result key)
    (entries : List (Entry Key Payload)) (key : Key) :
    Entry.lookup (entries.map (Entry.mapPayload change)) key =
      (Entry.lookup entries key).map (change key) := by
  have go (rest : List (Entry Key Payload)) (found : Option (Payload key)) :
      (rest.map (Entry.mapPayload change)).foldl
        (fun current (entry : Entry Key Result) =>
          letI : Decidable (key = entry.key) := entry.decideEq key
          if same : key = entry.key then some (same.symm ▸ entry.value) else current)
        (found.map (change key)) =
      (rest.foldl (fun current (entry : Entry Key Payload) =>
          letI : Decidable (key = entry.key) := entry.decideEq key
          if same : key = entry.key then some (same.symm ▸ entry.value) else current)
        found).map (change key) := by
    induction rest generalizing found with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.map_cons, List.foldl_cons, Entry.mapPayload]
      by_cases same : key = entry.key
      · subst key
        simpa using ih (some entry.value)
      · simpa [same] using ih found
  exact go entries none

/-- Wrap direct slot specifications without changing defaults or key order.
The supplied wrapper constructs each new slot specification. -/
def Declaration.mapSlots {Key : Type u} {Value : Key → Type v}
    (declaration : Declaration Key Value)
    (wrap : (key : Key) → SlotPayload Key Value key → SlotPayload Key Value key) :
    Declaration Key Value :=
  { declaration with slots := declaration.slots.map (Entry.mapPayload wrap) }

theorem Declaration.mapSlots_slot {Key : Type u} {Value : Key → Type v}
    (declaration : Declaration Key Value)
    (wrap : (key : Key) → SlotPayload Key Value key → SlotPayload Key Value key)
    (key : Key) :
    (declaration.mapSlots wrap).slot key = (declaration.slot key).map (wrap key) :=
  Entry.lookup_mapPayload wrap declaration.slots key

theorem Declaration.mapSlots_default {Key : Type u} {Value : Key → Type v}
    (declaration : Declaration Key Value)
    (wrap : (key : Key) → SlotPayload Key Value key → SlotPayload Key Value key)
    (key : Key) :
    (declaration.mapSlots wrap).default key = declaration.default key := rfl

/-- Transform each existing direct declaration in the current reachable
ancestry once. Keep absent declarations absent and preserve unrelated nodes.
The graph is unchanged, so the existing C4 certificate is retained. -/
def Plan.transformAncestryDeclarations {Key : Type u} {Value : Key → Type v}
    (plan : Plan Key Value)
    (change : String → Declaration Key Value → Declaration Key Value) :
    Plan Key Value :=
  let declarations := plan.precedence.foldl (fun table name =>
    table.insert name ((plan.schema.declaration name).map (change name)))
    ({} : Std.HashMap String (Option (Declaration Key Value)))
  let schema : Schema Key Value :=
    { plan.schema with
      declaration := fun name =>
        match declarations.get? name with
        | some declaration => declaration
        | none => plan.schema.declaration name }
  { plan with schema }

theorem Plan.transformAncestryDeclarations_precedence
    (plan : Plan Key Value)
    (change : String → Declaration Key Value → Declaration Key Value) :
    (plan.transformAncestryDeclarations change).precedence = plan.precedence := rfl

theorem Plan.transformAncestryDeclarations_graph
    (plan : Plan Key Value)
    (change : String → Declaration Key Value → Declaration Key Value) :
    (plan.transformAncestryDeclarations change).schema.graph = plan.schema.graph := rfl

private theorem lookup_outside (names : List String)
    (table : Std.HashMap String (Option (Declaration Key Value))) (query : String)
    (absent : query ∉ names)
    (getDeclaration : String → Option (Declaration Key Value)) :
    (names.foldl (fun table name => table.insert name (getDeclaration name)) table).get? query =
      table.get? query := by
  induction names generalizing table with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.foldl_cons]
    have different : name ≠ query := by
      intro same
      subst name
      simp at absent
    rw [ih (table.insert name (getDeclaration name)) (by
      intro member
      exact absent (List.mem_cons_of_mem name member))]
    simp [Std.HashMap.getElem?_insert, different]

private theorem lookup_preserves (names : List String)
    (table : Std.HashMap String (Option (Declaration Key Value))) (query : String)
    (getDeclaration : String → Option (Declaration Key Value))
    (present : table.get? query = some (getDeclaration query)) :
    (names.foldl (fun table name => table.insert name (getDeclaration name)) table).get? query =
      some (getDeclaration query) := by
  induction names generalizing table with
  | nil => exact present
  | cons name rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Std.HashMap.get?_insert]
    by_cases same : name = query
    · subst name
      simp
    · simpa [same] using present

private theorem lookup_present (names : List String)
    (table : Std.HashMap String (Option (Declaration Key Value))) (query : String)
    (getDeclaration : String → Option (Declaration Key Value))
    (member : query ∈ names) :
    (names.foldl (fun table name => table.insert name (getDeclaration name)) table).get? query =
      some (getDeclaration query) := by
  induction names generalizing table with
  | nil => simp at member
  | cons name rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | member
    · subst name
      apply lookup_preserves
      simp
    · exact ih (table.insert name (getDeclaration name)) member

/-- Every reachable declaration has precisely the specified transformation;
`none` remains `none`, without invoking a change on an empty substitute. -/
theorem Plan.transformAncestryDeclarations_inside
    (plan : Plan Key Value)
    (change : String → Declaration Key Value → Declaration Key Value)
    (name : String) (member : name ∈ plan.precedence) :
    (plan.transformAncestryDeclarations change).schema.declaration name =
      (plan.schema.declaration name).map (change name) := by
  unfold Plan.transformAncestryDeclarations
  have present := lookup_present plan.precedence {} name
    (fun name => (plan.schema.declaration name).map (change name)) member
  simp only [present]

/-- An unrelated branch keeps its original declaration lookup. -/
theorem Plan.transformAncestryDeclarations_outside
    (plan : Plan Key Value)
    (change : String → Declaration Key Value → Declaration Key Value)
    (name : String) (absent : name ∉ plan.precedence) :
    (plan.transformAncestryDeclarations change).schema.declaration name =
      plan.schema.declaration name := by
  unfold Plan.transformAncestryDeclarations
  have missing := lookup_outside plan.precedence {} name absent
    (fun name => (plan.schema.declaration name).map (change name))
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at missing
  simp only [Std.HashMap.get?_eq_getElem?, missing]

/-- Install a snapshot-wide declaration transformation with fresh lazy
cells. Resolution mode and validated C4 topology are retained. -/
def Memoized.transformAncestryDeclarations {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value)
    (change : String → Declaration Key Value → Declaration Key Value) :
    Memoized Key Value :=
  object.rebuild (object.plan.transformAncestryDeclarations change)

/-- Wrap existing direct methods throughout the current ancestry. The
wrapper receives the node identity and typed slot key, final self and next
remain available inside the returned ordinary slot specification. -/
def Memoized.wrapAncestrySlots {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value)
    (wrap : String → (key : Key) → SlotPayload Key Value key → SlotPayload Key Value key) :
    Memoized Key Value :=
  object.transformAncestryDeclarations fun name declaration =>
    declaration.mapSlots (wrap name)

end LeanPoo.Object
