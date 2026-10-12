import LeanPoo.Object.Recursive

open LeanPoo
open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.MutableRecord
namespace LeanPoo.Tests.ObjectSemantics

private def declarations (name : String) : Specification :=
  if name == "O" then .compose (.slot "x" (constant (.integer 1))) (.slot "y" (constant (.integer 2)))
  else if name == "B" then .slot "x" (constant (.integer 3))
  else if name == "A" then .slot "x" (modify fun value => match value with
    | .integer n => .integer (2 * n) | _ => value)
  else if name == "C" then .slot "z" (compute fun self =>
    (self "x").bind fun x => (self "y").map fun y => .list [x, y])
  else if name == "D" then .slot "x" (constant (.integer 10))
  else .identity

private def schema : Object.Recursive.Schema :=
  ⟨[("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["A", "B"]), ("D", ["C"])], declarations, {}⟩

private def run : IO Unit := do
  let c ← IO.ofExcept ((Object.Recursive.compile schema "C").mapError reprStr)
  let d ← IO.ofExcept ((Object.Recursive.compile schema "D").mapError reprStr)
  unless c.precedence == ["C", "A", "B", "O"] && c.read 3 "x" == .value (.integer 6) &&
      c.read 3 "z" == .value (.list [.integer 6, .integer 2]) &&
      d.read 3 "z" == .value (.list [.integer 10, .integer 2]) do
    throw (IO.userError "safe C3-to-composition-to-fix observation")
  unless c.read 1 "z" == .pending && c.read 3 "missing" == .error "missing slot: missing" do
    throw (IO.userError "pending and error boundary")
  let mutable ← c.mutable
  let alias := mutable
  mutable.slot "x" (constant (.integer 21))
  unless (← alias.read 3 "z") == .value (.list [.integer 21, .integer 2]) &&
      c.read 3 "z" == .value (.list [.integer 6, .integer 2]) do
    throw (IO.userError "safe object pure-to-mutable conversion")
  let recursive : Object.Recursive.Schema :=
    ⟨[("R", [])], fun _ => .compose (.slot "a" (compute fun self => self "b"))
      (.slot "b" (compute fun self => self "a")), {}⟩
  let loop ← IO.ofExcept ((Object.Recursive.compile recursive "R").mapError reprStr)
  unless loop.read 50 "a" == .pending do throw (IO.userError "mutual recursion observation")
  let failed := { schema with declaration := fun _ => .error "bad prototype" }
  unless Object.Recursive.compile failed "C" matches .error (.prototype "bad prototype") do
    throw (IO.userError "prototype admission error")
  unless Object.Recursive.compile schema "missing" matches .error (.topology (.unknownNode "missing")) do
    throw (IO.userError "topology admission error")
  IO.println "POOF-RECURSIVE-OBJECT-OK C3+dynamic+fix=connected allObservations=kernel unsafe=false mutableConversion=true"
#eval run
#print axioms Object.Recursive.Plan.read_derivation
#print axioms Object.Recursive.Plan.read_returns
#print axioms Object.Recursive.Plan.read_diverges
end LeanPoo.Tests.ObjectSemantics
