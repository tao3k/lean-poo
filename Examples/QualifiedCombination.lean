import LeanPoo.Object.MultimethodCombination
import LeanPoo.C4.Linearize

/-! A caller defines the meaning of two method qualifiers. Dispatch still
selects by a pair of C4 orders; the interpreter decides how validation and
rendering contributions work together. -/

namespace LeanPoo.Examples.QualifiedCombination

open LeanPoo

structure Request where
  rendererOrder : List String
  formatOrder : List String
  bytes : Nat

inductive Qualifier where
  | accept
  | render
  deriving DecidableEq

abbrev Body : Qualifier → Type
  | .accept => Nat → Bool
  | .render => Nat → String

def interpret (methods : Object.QualifiedMethods Qualifier Body)
    (request : Request) : Except String (List String) :=
  if (methods.lookup .accept).all (fun accepts => accepts request.bytes) then
    .ok ((methods.lookup .render).map (fun render => render request.bytes))
  else
    .error "payload rejected"

def generic : Object.Multimethod Request (Sigma Body)
    (Except String (List String)) :=
  Object.Multimethod.qualified 2
    (fun request => [request.rendererOrder, request.formatOrder]) interpret

def usage : Except String
    (Except String (List String) × Except String (List String)) := do
  let rendererGraph : C4.Graph :=
    { nodes := [{ name := "Renderer" },
      { name := "Fast", parentOrders := [["Renderer"]] }] }
  let formatGraph : C4.Graph :=
    { nodes := [{ name := "Text" },
      { name := "Json", parentOrders := [["Text"]] }] }
  let rendererOrder ← (C4.linearize rendererGraph "Fast").mapError
    (fun _ => "invalid renderer inheritance")
  let formatOrder ← (C4.linearize formatGraph "Json").mapError
    (fun _ => "invalid format inheritance")
  let methods ← (generic.register [.any, .any]
    ⟨.render, fun _ => "fallback"⟩).mapError (fun _ => "invalid arity")
  let methods ← (methods.register [.prototype "Fast", .prototype "Json"]
    ⟨.render, fun _ => "fast-json"⟩).mapError (fun _ => "invalid arity")
  let methods ← (methods.contribute [.prototype "Fast", .prototype "Json"]
    ⟨.accept, fun bytes => bytes <= 1024⟩).mapError
      (fun _ => "invalid arity")
  let input : Request := ⟨rendererOrder, formatOrder, 64⟩
  let (small, cached) ← (methods.call input).mapError
    (fun _ => "invalid call shape")
  let (large, _) ← (cached.call { input with bytes := 2048 }).mapError
    (fun _ => "invalid call shape")
  return (small, large)

#eval usage

end LeanPoo.Examples.QualifiedCombination
