import Init

/-! Receiver scopes for shared lexical slot bindings. The denotation is the
existing receiver-indexed lookup, with lexical closures retaining that receiver.
Gerbil syntax hygiene, read-only macro errors and mutation are executable premises;
these laws do not prove the host expander. -/
namespace LeanPoo.Functional.Parameters

/-- Supply one receiver's lookup to a body. Result may itself be a function,
multiple-result record, or explicit error; no field is precomputed here. -/
def withSlotScope (lookup : Receiver → Name → Value) (self : Receiver)
    (body : (Name → Value) → Result) : Result :=
  body (lookup self)

/-- Bare field references retain the chosen receiver and original key. -/
theorem withSlotScope_read (lookup : Receiver → Name → Value) (self : Receiver) (name : Name) :
    withSlotScope lookup self (fun fields => fields name) = lookup self name := rfl

/-- A callable field receives the same complete argument without rebinding self. -/
theorem withSlotScope_call (lookup : Receiver → Name → Argument → Result)
    (self : Receiver) (name : Name) (argument : Argument) :
    withSlotScope lookup self (fun fields => fields name argument) = lookup self name argument := rfl

/-- A nested receiver supplies its own fields without replacing captured outer fields. -/
theorem withSlotScope_nested (lookup : Receiver → Name → Value) (outer inner : Receiver)
    (outerName innerName : Name) (consume : Value → Value → Result) :
    withSlotScope lookup outer (fun outerFields =>
      withSlotScope lookup inner (fun innerFields => consume (outerFields outerName) (innerFields innerName))) =
      consume (lookup outer outerName) (lookup inner innerName) := rfl

/-- Delayed field access keeps its lexical owner when invoked from another scope. -/
theorem withSlotScope_capture (lookup : Receiver → Name → Value) (outer inner : Receiver) (name : Name) :
    withSlotScope lookup outer (fun fields => fun (_ : Receiver) => fields name) inner =
      lookup outer name := rfl

/-- Equivalent receiver lookups are interchangeable for the whole opaque body,
including its returned function/error. This does not infer effectful equivalence. -/
theorem withSlotScope_congr (lookup other : Receiver → Name → Value) (self : Receiver)
    (body : (Name → Value) → Result) (same : ∀ name, lookup self name = other self name) :
    withSlotScope lookup self body = withSlotScope other self body := by
  exact congrArg body (funext same)

/-- Current revision remains an input of a callable field: capturing its receiver
is not caching an old field result or substituting the nested receiver. -/
theorem withSlotScope_revision (lookup : Receiver → Name → Revision → Value)
    (self : Receiver) (name : Name) (revision : Revision) :
    withSlotScope lookup self (fun fields => fun current => fields name current) revision =
      lookup self name revision := rfl
variable {Name Value Result : Type}

/-- Lower resolved alias/key pairs to nested lexical scopes with the standard
right fold. Values may themselves be delayed computations; no read is selected
until the body uses the alias. Host identifier generation/hygiene is a premise. -/
def withSlotBindings [DecidableEq Name] (read : Name → Value)
    (bindings : List (Name × Name)) (environment : Name → Value)
    (body : (Name → Value) → Result) : Result :=
  bindings.foldr (fun binding next fields =>
    next (fun name => if name = binding.1 then read binding.2 else fields name)) body environment

/-- Independent recursive denotation of the former per-binding macro expansion. -/
def recursiveSlotBindings [DecidableEq Name] (read : Name → Value) :
    List (Name × Name) → (Name → Value) → ((Name → Value) → Result) → Result
  | [], fields, body => body fields
  | binding :: rest, fields, body =>
    recursiveSlotBindings read rest
      (fun name => if name = binding.1 then read binding.2 else fields name) body

/-- Empty binding groups do not inspect their reader. -/
theorem withSlotBindings_nil [DecidableEq Name] (read : Name → Value)
    (fields : Name → Value) (body : (Name → Value) → Result) :
    withSlotBindings read [] fields body = body fields := rfl

/-- Core lexical nesting extends the environment before expanding the suffix. -/
theorem withSlotBindings_cons [DecidableEq Name] (read : Name → Value)
    (binding : Name × Name) (rest) (fields : Name → Value) (body : (Name → Value) → Result) :
    withSlotBindings read (binding :: rest) fields body =
      withSlotBindings read rest
        (fun name => if name = binding.1 then read binding.2 else fields name) body := rfl

/-- Whole-fold lowering preserves arbitrary bodies, not just successful reads. -/
theorem withSlotBindings_recursive [DecidableEq Name] (read : Name → Value)
    (bindings : List (Name × Name)) (fields : Name → Value) (body : (Name → Value) → Result) :
    withSlotBindings read bindings fields body = recursiveSlotBindings read bindings fields body := by
  induction bindings generalizing fields with
  | nil => rfl
  | cons binding rest ih => exact ih _

/-- Separate alias groups compose in source order, with the second group inner. -/
theorem withSlotBindings_append [DecidableEq Name] (read : Name → Value)
    (first second : List (Name × Name)) (fields : Name → Value) (body : (Name → Value) → Result) :
    withSlotBindings read (first ++ second) fields body =
      withSlotBindings read first fields (fun outer => withSlotBindings read second outer body) := by
  induction first generalizing fields with
  | nil => rfl
  | cons binding rest ih => exact ih _

/-- Repeated aliases shadow earlier bindings, preserving the original nested scopes. -/
theorem withSlotBindings_shadow [DecidableEq Name] (read : Name → Value)
    (alias first last : Name) (fields : Name → Value) :
    withSlotBindings read [(alias, first), (alias, last)] fields (fun current => current alias) = read last := by
  simp [withSlotBindings]

/-- A body ignoring every alias cannot force any supplied field computation. -/
theorem withSlotBindings_unused [DecidableEq Name] (read : Name → Value)
    (bindings : List (Name × Name)) (fields : Name → Value) (result : Result) :
    withSlotBindings read bindings fields (fun _ => result) = result := by
  induction bindings generalizing fields with
  | nil => rfl
  | cons binding rest ih => exact ih _
/-- Core definition sequences evaluate and bind each snapshot before the suffix.
The supplied reader can inspect earlier definitions and retain external effects;
this is a denotation, not a claim about host definition installation. -/
def snapshotSlotBindings {m : Type → Type} [Monad m] [DecidableEq Name]
    (read : (Name → Value) → Name → m Value) (bindings : List (Name × Name))
    (fields : Name → Value) (body : (Name → Value) → m Result) : m Result :=
  bindings.foldr (fun binding next environment => do
    let value ← read environment binding.2
    next (fun name => if name = binding.1 then value else environment name)) body fields

/-- Independent specification of successive snapshot definitions. -/
def recursiveSnapshotBindings {m : Type → Type} [Monad m] [DecidableEq Name]
    (read : (Name → Value) → Name → m Value) :
    List (Name × Name) → (Name → Value) → ((Name → Value) → m Result) → m Result
  | [], fields, body => body fields
  | binding :: rest, fields, body => do
    let value ← read fields binding.2
    recursiveSnapshotBindings read rest
      (fun name => if name = binding.1 then value else fields name) body

/-- An empty definition sequence selects only its body, not its reader. -/
theorem snapshotSlotBindings_nil {m : Type → Type} [Monad m] [DecidableEq Name]
    (read : (Name → Value) → Name → m Value) (fields : Name → Value)
    (body : (Name → Value) → m Result) : snapshotSlotBindings read [] fields body = body fields := rfl

/-- Each snapshot is read before later bindings or the consumer are selected. -/
theorem snapshotSlotBindings_cons {m : Type → Type} [Monad m] [DecidableEq Name]
    (read : (Name → Value) → Name → m Value) (binding : Name × Name) (rest)
    (fields : Name → Value) (body : (Name → Value) → m Result) :
    snapshotSlotBindings read (binding :: rest) fields body = (do
      let value ← read fields binding.2
      snapshotSlotBindings read rest (fun name => if name = binding.1 then value else fields name) body) := rfl

/-- Standard sequencing equals recursive expansion for any supplied monad. -/
theorem snapshotSlotBindings_recursive {m : Type → Type} [Monad m] [DecidableEq Name]
    (read : (Name → Value) → Name → m Value) (bindings : List (Name × Name))
    (fields : Name → Value) (body : (Name → Value) → m Result) :
    snapshotSlotBindings read bindings fields body = recursiveSnapshotBindings read bindings fields body := by
  induction bindings generalizing fields with
  | nil => rfl
  | cons binding rest ih =>
    rw [snapshotSlotBindings_cons]
    simp only [recursiveSnapshotBindings]
    congr 1
    funext value
    exact ih _

/-- A failed snapshot propagates its exact error without selecting later reads. -/
theorem snapshotSlotBindings_refused [DecidableEq Name]
    (read : (Name → Value) → Name → Except String Value) (binding : Name × Name) (rest)
    (fields : Name → Value) (body : (Name → Value) → Except String Result) (message)
    (failed : read fields binding.2 = .error message) :
    snapshotSlotBindings read (binding :: rest) fields body = .error message := by
  rw [snapshotSlotBindings_cons, failed]
  rfl

/-- Select one spelling bucket without identifying distinct lexical scopes.
The full identifier equality remains authoritative; the spelling is only an index. -/
def matchingSlotIdentifiers {Identifier Spelling : Type} [DecidableEq Spelling]
    (spelling : Identifier → Spelling) (query : Identifier) (seen : List Identifier) :=
  seen.filter (fun candidate => decide (spelling candidate = spelling query))

/-- Equal full identifiers always share a spelling bucket. Hash collisions and
same-spelling identifiers with distinct marks cannot change membership. -/
theorem mem_matchingSlotIdentifiers {Identifier Spelling : Type} [DecidableEq Spelling]
    (spelling : Identifier → Spelling) (query : Identifier) (seen : List Identifier) :
    query ∈ matchingSlotIdentifiers spelling query seen ↔ query ∈ seen := by
  simp [matchingSlotIdentifiers]

/-- First-occurrence selection with a complete identifier comparison, independent
of the compiler table implementation. It retains the original supplied values. -/
def retainSlotIdentifiers {Identifier : Type} [DecidableEq Identifier] :
    List Identifier → List Identifier → List Identifier
  | _, [] => []
  | seen, query :: rest =>
    if query ∈ seen then retainSlotIdentifiers seen rest
    else query :: retainSlotIdentifiers (query :: seen) rest

/-- The indexed selector uses spelling only to narrow full equality candidates.
The host's consistent hash, resizing and syntax representation remain premises. -/
def retainIndexedSlotIdentifiers {Identifier Spelling : Type}
    [DecidableEq Identifier] [DecidableEq Spelling] (spelling : Identifier → Spelling) :
    List Identifier → List Identifier → List Identifier
  | _, [] => []
  | seen, query :: rest =>
    if query ∈ matchingSlotIdentifiers spelling query seen
    then retainIndexedSlotIdentifiers spelling seen rest
    else query :: retainIndexedSlotIdentifiers spelling (query :: seen) rest

/-- Indexing preserves the entire retained sequence, including scoped identities
and declaration order; it does not replace full equality with spelling equality. -/
theorem retainIndexedSlotIdentifiers_eq {Identifier Spelling : Type}
    [DecidableEq Identifier] [DecidableEq Spelling] (spelling : Identifier → Spelling)
    (seen inputs : List Identifier) :
    retainIndexedSlotIdentifiers spelling seen inputs = retainSlotIdentifiers seen inputs := by
  induction inputs generalizing seen with
  | nil => rfl
  | cons query rest ih =>
    simp only [retainIndexedSlotIdentifiers, retainSlotIdentifiers, mem_matchingSlotIdentifiers]
    split <;> simp only [ih]

/-- A spelling bucket contains no more candidates than the complete prior set.
This bounds logical equality candidates, excluding hashing, allocation and GC. -/
theorem matchingSlotIdentifiers_length_le {Identifier Spelling : Type} [DecidableEq Spelling]
    (spelling : Identifier → Spelling) (query : Identifier) (seen : List Identifier) :
    (matchingSlotIdentifiers spelling query seen).length ≤ seen.length :=
  List.length_filter_le _ _

/-- A fresh spelling has no full-equality candidates. Same-spelling distinct
scopes remain in its bucket and still require the original equality check. -/
theorem matchingSlotIdentifiers_fresh {Identifier Spelling : Type} [DecidableEq Spelling]
    (spelling : Identifier → Spelling) (query : Identifier) (seen : List Identifier)
    (fresh : ∀ candidate ∈ seen, spelling candidate ≠ spelling query) :
    matchingSlotIdentifiers spelling query seen = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro candidate member
  simp [fresh candidate member]

end LeanPoo.Functional.Parameters
