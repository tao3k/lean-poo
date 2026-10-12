import LeanPoo.Prototype.DynamicValueEquality

open LeanPoo.Prototype.Dynamic
namespace LeanPoo.Tests.DynamicValueEquality

example (left right : Value) : left.equalAt left.wireDepth right = true ↔ left = right :=
  left.equalAt_correct right left.wireDepth (Nat.le_refl _)

private def checks : IO Unit := do
  let nested : Value := (List.range 128).foldl (fun value _ => .list [value])
    (.integer (-123456789012345678901234567890))
  unless decide (nested = nested) do throw (IO.userError "nested argument equality")
  let differences : List (Value × Value) :=
    [(.unit, .list []), (.boolean false, .integer 0), (.text "λ", .text "Λ"),
      (.integer 123456789012345678901234567890, .integer 123456789012345678901234567891),
      (.function "same", .descriptor "same"), (.function "f", .function "g"),
      (.descriptor "A", .descriptor "B"), (.list [.integer 1, .integer 2], .list [.integer 2, .integer 1]),
      (.dictionary [(.text "k", .integer 1), (.text "k", .integer 2)],
        .dictionary [(.text "k", .integer 2), (.text "k", .integer 1)]),
      (.object [("x", .integer 1), ("x", .integer 2)], .object [("x", .integer 1)]),
      (.object [("x", .integer 1), ("y", .unit)], .object [("y", .unit), ("x", .integer 1)])]
  for (left, right) in differences do
    unless !decide (left = right) && !decide (right = left) do
      throw (IO.userError "distinct dynamic arguments alias one cache request")
  IO.println s!"DYNAMIC-VALUE-EQUALITY-OK nesting=128 distinctPairs={differences.length} kernel=true"

#eval checks
#print axioms Value.equalAt_correct
end LeanPoo.Tests.DynamicValueEquality
