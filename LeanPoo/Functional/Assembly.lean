import LeanPoo.C4.Renaming

/-! C4 selection of typed, context-dependent factories. Selection resolves
function values before applying a context; mathematical factories can remain
noncomputable, while provider selection is executable. -/
namespace LeanPoo.Functional

universe u v w x

/-- Every factory returns a value indexed by the same supplied context.
The result may bundle data and proofs depending on that data. -/
abbrev Factory (Context : Type u) (Result : Context → Type v) :=
  (context : Context) → Result context

namespace Factory

/-- Transform a factory's result while keeping its exact context index. -/
def map {Context : Type u} {Input : Context → Type v} {Output : Context → Type w}
    (change : ∀ context, Input context → Output context) (factory : Factory Context Input) :
    Factory Context Output := fun context => change context (factory context)

@[simp] theorem map_apply {Context : Type u} {Input : Context → Type v} {Output : Context → Type w}
    (change : ∀ context, Input context → Output context) (factory : Factory Context Input)
    (context : Context) : map change factory context = change context (factory context) := rfl

theorem map_identity {Context : Type u} {Input : Context → Type v} (factory : Factory Context Input) :
    map (fun _ value => value) factory = factory := rfl

theorem map_compose {Context : Type u} {Input : Context → Type v}
    {Middle : Context → Type w} {Output : Context → Type x}
    (first : ∀ context, Input context → Middle context)
    (second : ∀ context, Middle context → Output context) (factory : Factory Context Input) :
    map second (map first factory) = map (fun context value => second context (first context value)) factory := rfl

/-- Choose the next factory from a result and invoke it at the same context.
This composes explicit producers; it does not infer their requirements. -/
def bind {Context : Type u} {Input : Context → Type v} {Output : Context → Type w}
    (factory : Factory Context Input)
    (next : ∀ context, Input context → Factory Context Output) : Factory Context Output :=
  fun context => next context (factory context) context

@[simp] theorem bind_apply {Context : Type u} {Input : Context → Type v} {Output : Context → Type w}
    (factory : Factory Context Input) (next : ∀ context, Input context → Factory Context Output)
    (context : Context) : bind factory next context = next context (factory context) context := rfl

theorem bind_assoc {Context : Type u} {Input : Context → Type v}
    {Middle : Context → Type w} {Output : Context → Type x}
    (factory : Factory Context Input) (first : ∀ context, Input context → Factory Context Middle)
    (second : ∀ context, Middle context → Factory Context Output) :
    bind (bind factory first) second = bind factory (fun context value => bind (first context value) second) := rfl

/-- Select a factory at application time using the supplied context. -/
def choose {Context : Type u} {Result : Context → Type v}
    (condition : Context → Bool) (whenTrue whenFalse : Factory Context Result) :
    Factory Context Result := fun context =>
  if condition context then whenTrue context else whenFalse context

theorem choose_true {Context : Type u} {Result : Context → Type v}
    (condition : Context → Bool) (whenTrue whenFalse : Factory Context Result)
    (context : Context) (yes : condition context = true) :
    choose condition whenTrue whenFalse context = whenTrue context := by
  simp [choose, yes]

theorem choose_false {Context : Type u} {Result : Context → Type v}
    (condition : Context → Bool) (whenTrue whenFalse : Factory Context Result)
    (context : Context) (no : condition context = false) :
    choose condition whenTrue whenFalse context = whenFalse context := by
  simp [choose, no]

/-- Apply a list of retained factories at one context, preserving its order. -/
def sequence {Context : Type u} {Result : Context → Type v}
    (factories : List (Factory Context Result)) : Factory Context (fun context => List (Result context)) :=
  fun context => factories.map (fun factory => factory context)

@[simp] theorem sequence_append {Context : Type u} {Result : Context → Type v}
    (left right : List (Factory Context Result)) (context : Context) :
    sequence (left ++ right) context = sequence left context ++ sequence right context := by
  simp [sequence]

@[simp] theorem sequence_length {Context : Type u} {Result : Context → Type v}
    (factories : List (Factory Context Result)) (context : Context) :
    (sequence factories context).length = factories.length := by
  simp [sequence]

/-- Aggregate factory results in list order at the same context. Every listed
factory is applied; error-valued results follow the supplied combine policy. -/
def fold {Context : Type u} {Result : Context → Type v} {Acc : Context → Type w}
    (combine : ∀ context, Acc context → Result context → Acc context)
    (initial : Factory Context Acc) (factories : List (Factory Context Result)) : Factory Context Acc :=
  fun context => factories.foldl (fun acc factory => combine context acc (factory context)) (initial context)

theorem fold_sequence {Context : Type u} {Result : Context → Type v} {Acc : Context → Type w}
    (combine : ∀ context, Acc context → Result context → Acc context)
    (initial : Factory Context Acc) (factories : List (Factory Context Result)) (context : Context) :
    fold combine initial factories context = (sequence factories context).foldl (combine context) (initial context) := by
  simp [fold, sequence, List.foldl_map]

theorem fold_append {Context : Type u} {Result : Context → Type v} {Acc : Context → Type w}
    (combine : ∀ context, Acc context → Result context → Acc context)
    (initial : Factory Context Acc) (left right : List (Factory Context Result)) :
    fold combine initial (left ++ right) = fold combine (fold combine initial left) right := by
  funext context
  simp [fold, List.foldl_append]

/-- Recover a context-dependent domain error. Successful results are retained
exactly; the handler's result, including a second error, is returned unchanged. -/
def recover {Context : Type u} {Result : Context → Type v} {Error : Type w}
    (attempt : Factory Context (fun context => Except Error (Result context)))
    (handler : Error → Factory Context (fun context => Except Error (Result context))) :
    Factory Context (fun context => Except Error (Result context)) := fun context =>
  match attempt context with
  | .ok value => .ok value
  | .error error => handler error context

theorem recover_ok {Context : Type u} {Result : Context → Type v} {Error : Type w}
    (attempt : Factory Context (fun context => Except Error (Result context)))
    (handler : Error → Factory Context (fun context => Except Error (Result context)))
    (context : Context) (value : Result context) (success : attempt context = .ok value) :
    recover attempt handler context = .ok value := by
  simp [recover, success]

theorem recover_error {Context : Type u} {Result : Context → Type v} {Error : Type w}
    (attempt : Factory Context (fun context => Except Error (Result context)))
    (handler : Error → Factory Context (fun context => Except Error (Result context)))
    (context : Context) (error : Error) (failed : attempt context = .error error) :
    recover attempt handler context = handler error context := by
  simp [recover, failed]

/-- Preserve an existing context-indexed theorem as a proof-bearing factory.
PLift changes its sort, not its proposition, data, or guards. -/
def fromProof {Context : Type u} {Claim : Context → Prop}
    (prove : ∀ context, Claim context) : Factory Context (fun context => PLift (Claim context)) :=
  fun context => ⟨prove context⟩

@[simp] theorem fromProof_down {Context : Type u} {Claim : Context → Prop}
    (prove : ∀ context, Claim context) (context : Context) :
    (fromProof prove context).down = prove context := rfl

/-- Adapt a factory to a larger context by an explicit projection. Its result
is indexed by that projection; this does not transport a witness to new data. -/
def reindex {Context : Type u} {Result : Context → Type v} {Outer : Type w}
    (project : Outer → Context) (factory : Factory Context Result) :
    Factory Outer (fun outer => Result (project outer)) :=
  fun outer => factory (project outer)

/-- Combine retained factories at the same context. The consumer may use both
data and proof witnesses to construct its own context-indexed result. -/
def zipWith {Context : Type u} {Left : Context → Type v}
    {Right : Context → Type w} {Result : Context → Type x}
    (combine : (context : Context) → Left context → Right context → Result context)
    (left : Factory Context Left) (right : Factory Context Right) : Factory Context Result :=
  fun context => combine context (left context) (right context)

end Factory

/-- A provider owns an optional factory at each typed capability key. -/
abbrev Provider (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) :=
  (key : Key) → Option (Factory Context (fun context => Value context key))

variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Compose capability dictionaries: a provided child factory overrides its
parent at that key; absent child capabilities fall through without invocation. -/
def Provider.compose (child parent : Provider Context Key Value) : Provider Context Key Value :=
  fun key => (child key).orElse (fun _ => parent key)

theorem Provider.compose_provided (child parent : Provider Context Key Value) (key : Key)
    (factory : Factory Context (fun context => Value context key))
    (provided : child key = some factory) : compose child parent key = some factory := by
  simp [compose, provided]

theorem Provider.compose_inherited (child parent : Provider Context Key Value) (key : Key)
    (absent : child key = none) : compose child parent key = parent key := by
  simp [compose, absent]

theorem Provider.compose_assoc (outer middle inner : Provider Context Key Value) :
    compose (compose outer middle) inner = compose outer (compose middle inner) := by
  funext key
  unfold compose
  cases outer key <;> cases middle key <;> rfl

/-- Choose the first available factory in an already computed precedence.
Factories are returned as functions and are not invoked during selection. -/
def select (names : List String) (providers : String → Provider Context Key Value)
    (key : Key) : Option (Factory Context (fun context => Value context key)) :=
  match names with
  | [] => none
  | name :: rest => match providers name key with
    | some factory => some factory
    | none => select rest providers key

/-- Resolve capabilities against a retained verified C4 order. -/
def assemble (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) : Provider Context Key Value :=
  select order.output providers

variable {names rest : List String} {name : String}
  {providers : String → Provider Context Key Value} {key : Key}
  {factory : Factory Context (fun context => Value context key)}

/-- Select once, then retain and reuse the returned factory for many contexts. -/
theorem select_head (provided : providers name key = some factory) :
    select (name :: rest) providers key = some factory := by
  simp [select, provided]

theorem select_skip (absent : providers name key = none) :
    select (name :: rest) providers key = select rest providers key := by
  simp [select, absent]

/-- A selected function is supplied by an actual member of the precedence. -/
theorem select_origin (selected : select names providers key = some factory) :
    ∃ name ∈ names, providers name key = some factory := by
  induction names with
  | nil => simp [select] at selected
  | cons name rest ih =>
    cases provided : providers name key with
    | none =>
      obtain ⟨source, member, same⟩ := ih (by simpa [select, provided] using selected)
      exact ⟨source, by simp [member], same⟩
    | some actual =>
      have same : actual = factory := by simpa [select, provided] using selected
      exact ⟨name, by simp, same ▸ provided⟩

/-- The chosen provider is an ancestor on the original graph. Selection alone
does not establish a mathematical contract beyond the factory's result type. -/
theorem assemble_origin {order : C4.VerifiedOrder graph root}
    (selected : assemble order providers key = some factory) :
    ∃ name, C4.Ancestor graph name root ∧ providers name key = some factory := by
  obtain ⟨name, member, same⟩ := select_origin selected
  exact ⟨name, order.covers.mp member, same⟩

/-- Aligned provider names preserve first-provider selection. Alignment is
required only on this precedence; no inverse dictionary or key cast is used. -/
theorem select_rename (rename : String → String)
    (mapped : String → Provider Context Key Value)
    (aligned : ∀ name ∈ names, mapped (rename name) key = providers name key) :
    select (names.map rename) mapped key = select names providers key := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have head := aligned name (by simp)
    have tail := ih (fun other member => aligned other (by simp [member]))
    simp only [List.map_cons, select, head]
    cases providers name key <;> simp_all

/-- The retained graph-renaming proof also preserves consumer capability
selection when providers are aligned on original ancestors. -/
theorem assemble_rename (order : C4.VerifiedOrder graph root)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map C4.Node.name).Nodup)
    (mapped : String → Provider Context Key Value)
    (aligned : ∀ name, C4.Ancestor graph name root →
      mapped (rename name) key = providers name key) :
    assemble (order.rename rename injective unique) mapped key =
      assemble order providers key := by
  apply select_rename
  intro name member
  exact aligned name (order.covers.mp member)

/-- Invoke a retained provider with the exact context determining its result. -/
def apply (provider : Provider Context Key Value) (context : Context) (key : Key) :
    Option (Value context key) := (provider key).map (fun factory => factory context)

/-- Resolve a required capability before invoking any factory. Failure returns
the missing typed key; success is a function reusable across contexts. -/
def require (provider : Provider Context Key Value) (key : Key) :
    Except Key (Factory Context (fun context => Value context key)) :=
  match provider key with
  | none => .error key
  | some factory => .ok factory

theorem require_ok_iff {provider : Provider Context Key Value} :
    require provider key = .ok factory ↔ provider key = some factory := by
  unfold require
  cases provider key <;> simp

theorem require_missing_iff {provider : Provider Context Key Value} :
    require provider key = .error key ↔ provider key = none := by
  unfold require
  cases provider key <;> simp

theorem apply_selected {provider : Provider Context Key Value} {context : Context}
    (selected : provider key = some factory) :
    apply provider context key = some (factory context) := by
  simp [apply, selected]

end LeanPoo.Functional
