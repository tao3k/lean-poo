import LeanPoo.C4.VerifiedOrder

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
