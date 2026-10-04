import LeanPoo.C4.ParentInvariant

namespace LeanPoo.Tests.ParentInvariant
open C4 LinearizeState

private def table : Table := ({} : Table)
  |>.insert "A" ⟨["A", "T"], some "T", some "T"⟩
  |>.insert "B" ⟨["B"], none, none⟩
private def node : Node :=
  { name := "Root", parentOrders := [[], ["B", "A", "B"], ["A", "B"], []] }

#guard unique ["B", "A", "B", "A", "C", "B"] == ["B", "A", "C"]
#guard parents node == ["B", "A"]
#guard match collectParents table (parents node) with
  | .ok entries => entries.map (·.precedence) == [["B"], ["A", "T"]]
  | _ => false
#guard match collectParents table ["A", "B", "A"] with
  | .ok entries => entries.map (·.precedence) == [["A", "T"], ["B"], ["A", "T"]]
  | _ => false
#guard match collectParents table ["A", "Missing1", "Missing2"] with
  | .error (.unknownNode name) => name == "Missing1"
  | _ => false
#guard match collectParents table ["Missing2", "Missing1", "A"] with
  | .error (.unknownNode name) => name == "Missing2"
  | _ => false
#guard match collectParents ({} : Table) [] with
  | .ok [] => true
  | _ => false

example (items : List String) : unique items = firstOccurrences {} items := unique_firstOccurrences items
example : name ∈ parents node ↔ name ∈ node.parentOrders.flatten := parents_mem
example (node : Node) : (parents node).Nodup := parents_nodup node
example (aligned : ListAligned (fun name entry => lookup table name = some entry) names entries) :
    collectParents table names = .ok entries := collectParents_complete aligned
example (success : collectParents table names = .ok entries) :
    ListAligned (fun name entry => lookup table name = some entry) names entries :=
  collectParents_sound success
example : (∃ entries, collectParents table (parents node) = .ok entries) ↔
    ∀ name ∈ node.parentOrders.flatten, ∃ entry, lookup table name = some entry :=
  collectParents_success_iff
example (valid : CacheInvariant graph cache)
    (trace : GraphTrace graph declaration.name output tail)
    (found : graph.findNode? declaration.name = some declaration)
    (success : collectParents cache (parents declaration) = .ok entries) (member : entry ∈ entries) :
    ∃ name ∈ declaration.parentOrders.flatten, ∃ parentTail,
      lookup cache name = some entry ∧ GraphTrace graph name entry.precedence parentTail ∧
      entry.precedence.Sublist output := collected_parent_preserves valid trace found success member

#print axioms ListAligned.length_eq
#print axioms unique_firstOccurrences
#print axioms unique_mem
#print axioms unique_nodup
#print axioms unique_sublist
#print axioms parents_mem
#print axioms parents_nodup
#print axioms parents_sublist
#print axioms collectParents_complete
#print axioms collectParents_sound
#print axioms collectParents_length
#print axioms collectParents_success_iff
#print axioms collected_parent_preserves
#print axioms cached_graph_rows

/- Original runtime collection loop retained as a refactor regression oracle. -/
private def originalCollection (cache : Table) (names : List String) :
    Except Error (List Linearization) := do
  let mut reversed := []
  for name in names do
    let some entry := lookup cache name | throw (.unknownNode name)
    reversed := entry :: reversed
  return reversed.reverse

private def sameResult [BEq α] (left right : Except Error α) : Bool :=
  match left, right with
  | .ok first, .ok second => first == second
  | .error first, .error second => first == second
  | _, _ => false
private def words : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => ["A", "B", "Missing1", "Missing2"].map (· :: rest)

#eval do
  let families := (List.range 6).flatMap words
  for names in families do
    unless unique names == names.eraseDups do
      throw (IO.userError s!"first-occurrence mismatch: {repr names}")
    unless sameResult (collectParents table names) (originalCollection table names) do
      throw (IO.userError s!"parent collection mismatch: {repr names}")
    unless sameResult (collectParents table (unique names)) (originalCollection table names.eraseDups) do
      throw (IO.userError s!"deduplicated parent collection mismatch: {repr names}")
  IO.println s!"PARENT-INVARIANT-OK families={families.length}"

end LeanPoo.Tests.ParentInvariant
