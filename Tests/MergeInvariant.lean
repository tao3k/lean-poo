import LeanPoo.C4.MergeInvariant

namespace LeanPoo.Tests.MergeInvariant
open C4 MergeState Precedence

private def repeated : List (List String) := [["A", "B", "B"], ["C", "B"], ["A", "B"]]
#guard (ancestorCounts repeated).getD "B" 0 == 4
#guard (ancestorCounts repeated).getD "A" 0 == 0
#guard (ancestorCounts repeated).getD "Missing" 0 == 0
#guard (exposedHeads repeated "A") == ["B", "B"]
private def afterA := (mergeStep [] repeated (ancestorCounts repeated)).toOption
#guard afterA.map (·.1) == some ["A"]
#guard afterA.map (·.2.1) == some [["B", "B"], ["C", "B"], ["B"]]
#guard afterA.map (fun state => state.2.2.getD "B" 0) == some 2
#guard (merge repeated).toOption.isNone
#guard (merge [[], ["A"], [], ["B", "A"], []]).toOption == some ["B", "A"]
#guard (merge [["A", "B"], ["B", "A"]]).toOption.isNone
#guard (mergeCertified [["A", "B"], ["C", "B"]]).toOption.map (·.output) == some ["A", "C", "B"]

example (lists : List (List String)) : CountInvariant lists (ancestorCounts lists) :=
  ancestorCounts_invariant lists
example (valid : CountInvariant lists counts) (name : String) :
    (counts.getD name 0 == 0) = eligible lists name := zero_iff_eligible valid name
example (trace : Trace lists output) : merge lists = .ok output := merge_complete trace
example (success : merge lists = .ok output) : Trace lists output := merge_sound success
example (lists : List (List String)) :
    (merge lists).toOption = (mergeReference lists).toOption.map (·.output) := merge_reference_output
example (trace : Trace lists output) :
    ∃ certificate, mergeCertified lists = .ok certificate ∧ certificate.output = output :=
  mergeCertified_complete trace

#print axioms ancestorCounts_invariant
#print axioms zero_iff_eligible
#print axioms tail_count_advance
#print axioms decrement_preserves
#print axioms eligibleHead_eq_choose
#print axioms trace_pending
#print axioms mergeStep_selected
#print axioms rounds_complete
#print axioms merge_complete
#print axioms rounds_sound
#print axioms merge_sound
#print axioms merge_success_iff
#print axioms merge_reference_output
#print axioms check_complete
#print axioms mergeCertified_complete
#print axioms mergeCertified_success_iff

private def words : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => ["A", "B"].map (· :: rest)

/- Exhaust all candidate families of up to three orders, each with up to
three positions over two names. Includes duplicates, empties, and conflicts. -/
#eval do
  let orders : List (List String) := (List.range 4).flatMap words
  let families : List (List (List String)) := [[]] ++ orders.map (fun a => [a]) ++
    orders.flatMap (fun a => orders.map (fun b => [a, b])) ++
    orders.flatMap (fun a => orders.flatMap (fun b => orders.map (fun c => [a, b, c])))
  for lists in families do
    let expected := (mergeReference lists).toOption.map (fun certificate : Certified lists => certificate.output)
    unless (merge lists).toOption == expected do
      throw (IO.userError s!"optimized/reference mismatch: {repr lists}")
    unless (mergeCertified lists).toOption.map (fun certificate : Certified lists => certificate.output) == expected do
      throw (IO.userError s!"certified/reference mismatch: {repr lists}")
  IO.println s!"MERGE-INVARIANT-OK families={families.length}"

end LeanPoo.Tests.MergeInvariant
