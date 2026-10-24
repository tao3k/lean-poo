import LeanPoo.Functional.RecursiveGeneration

/-! Shared recursive descriptor grammar: an integer leaf or a list of recursive
children. A finite choice script stands for deterministic PRNG decisions; scalar
values and actual host distributions are intentionally outside this fixture. -/
namespace Examples.RecursiveGenerators
open LeanPoo.Functional.RecursiveGeneration

/-- 0 is the recursive Union, 1 its scalar leaf, 2 a List of width at most two. -/
def tree : Grammar
  | 0 => [[1], [2]]
  | 1 => [[]]
  | 2 => [[], [0], [0, 0]]
  | _ => []

/-- A replayable finite chooser stream preserves opaque callback failure text. -/
def script : Choose (List (List Nat)) := fun _ _ _ choices =>
  match choices with
  | [] => .error "choices exhausted"
  | head :: tail => .ok (head, tail)

/-- Both recursive children refer to the same descriptor, not copied definitions. -/
def choices : List (List Nat) := [[2], [0, 0], [1], [], [1], []]
/-- Six actual productions witness the recursive value and its two leaves. -/
def trace : List Entry := [(0, [2]), (2, [0, 0]), (0, [1]), (1, []), (0, [1]), (1, [])]
/-- A smaller leaf remains in exactly the same recursive root domain. -/
def leaf : List Entry := [(0, [1]), (1, [])]

example : construct tree script 6 [(0, 5)] choices = .ok (trace, []) := by rfl
example : check tree 6 [(0, 5)] trace = true := by decide
example : construct tree script 5 [(0, 5)] choices = .error .nodes := by rfl
example : construct tree script 6 [(0, 3)] choices = .error .depth := by rfl
example : construct tree script 6 [(0, 5)] [[9]] = .error .choice := by rfl
example : construct tree script 6 [(0, 5)] [] = .error (.callback "choices exhausted") := by rfl
example : check tree 6 [(0, 0)] trace = false := by decide
example : check tree 6 [(0, 5)] (trace.take 3) = false := by decide
example : LeanPoo.Prototype.Recursive.solve (program tree script) 7 (6, [(0, 5)], choices) = .value (.ok (trace, [])) := by rfl
example : LeanPoo.Prototype.Recursive.solve (program tree script) 1 (6, [(0, 5)], choices) = .pending := by rfl
example : min (5 + 1) (1000000 : Nat) ≤ 5 ↔ (1000000 : Nat) ≤ 5 := saturation_feasible _ _

/-- A deliberately false size claim retains a valid finite boundary witness. -/
def fails (entries : List Entry) : Bool := decide (2 ≤ entries.length)
example : (LeanPoo.Functional.PropertyTesting.shrink (check tree 6 [(0, 5)]) fails List.length
    8 trace [[], trace, leaf, []]).1 = leaf := by decide
example : check tree 6 [(0, 5)] leaf = true ∧ fails leaf = true := by decide
end Examples.RecursiveGenerators
