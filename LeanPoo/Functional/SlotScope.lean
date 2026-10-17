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
end LeanPoo.Functional.Parameters
