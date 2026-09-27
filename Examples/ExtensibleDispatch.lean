import LeanPoo.Object.DispatchTable
import LeanPoo.Object.Memo

/-! A renderer and a format have independent C4 lineages. A plugin adds
methods for their *pair* after both lineages and the generic already exist.
The old table remains a usable snapshot. -/

namespace LeanPoo.Examples.ExtensibleDispatch

open LeanPoo

abbrev Payload : String → Type := fun _ => Nat

structure Request where
  renderer : Object.Plan String Payload
  format : Object.Plan String Payload
  bytes : Nat

inductive Operation where
  | render
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Args (_ : Operation) := Request
abbrev Method (_ : Operation) := String
abbrev Result (_ : Operation) := List String
abbrev Table := Object.DispatchTable Operation Args Method Result

def render : Object.Multimethod Request String (List String) :=
  { arity := 2
    precedence := fun request =>
      [request.renderer.precedence, request.format.precedence]
    combine := fun methods _ => methods.toList }

def request : Except C4.Error Request := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let baseRenderer ← LeanPoo.mix empty "Renderer" [] Object.Declaration.empty
  let fast ← LeanPoo.extend baseRenderer.schema "Fast" "Renderer"
    Object.Declaration.empty
  let baseFormat ← LeanPoo.mix empty "Text" [] Object.Declaration.empty
  let json ← LeanPoo.extend baseFormat.schema "Json" "Text"
    Object.Declaration.empty
  return ⟨fast, json, 64⟩

def baseTable : Except (Object.DispatchTableError Operation) Table := do
  let table := (Object.DispatchTable.empty : Table).install .render render
  table.register .render [.any, .any] "fallback"

def plugin : Object.DispatchTable.Edit (Key := Operation) (Args := Args)
    (Method := Method) (Result := Result) Unit := do
  Object.DispatchTable.registerIn .render
    [.prototype "Fast", .prototype "Json"] "json"
  Object.DispatchTable.registerWhenIn .render
    [.prototype "Fast", .prototype "Json"]
    (fun input => input.bytes > 100) "bulk-json"

def usage : Except String
    (List String × List String × List String × List String) := do
  let input ← request.mapError (fun _ => "invalid prototype graph")
  let original ← baseTable.mapError (fun _ => "invalid generic")
  let (before, warmed) ← (original.call .render input).mapError
    (fun _ => "invalid dispatch")
  let (_, extended) ← (plugin.run warmed).mapError
    (fun _ => "invalid plugin")
  let (small, extended) ← (extended.call .render input).mapError
    (fun _ => "invalid dispatch")
  let (bulk, _) ← (extended.call .render { input with bytes := 256 }).mapError
    (fun _ => "invalid dispatch")
  let (oldAgain, _) ← (warmed.call .render input).mapError
    (fun _ => "invalid dispatch")
  return (before, small, bulk, oldAgain)

#eval usage

end LeanPoo.Examples.ExtensibleDispatch
