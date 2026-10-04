import LeanPoo.C4.GraphCertificate

namespace LeanPoo.Tests.ReferenceMerge
open C4 Precedence

private def output (lists : List (List String)) := (mergeReference lists).toOption.map (·.output)
#guard output [] == some []
#guard output [[], []] == some []
#guard output [["A"], ["B", "A"]] == some ["B", "A"]
#guard output [["A", "B"], ["C", "B"]] == some ["A", "C", "B"]
#guard output [["A", "B"], ["A", "B"]] == some ["A", "B"]
#guard output [["A", "B"], ["B", "A"]] == none
#guard output [["A", "A"]] == none
#guard (mergeReferenceWithFuel [["A"]] 0).toOption.isNone
#guard (mergeReferenceWithFuel [["A"]] 1).toOption.map (·.output) == some ["A"]
#guard (mergeReferenceWithFuel [] 0).toOption.map (·.output) == some []
#guard (mergeWithSuffixReference [["X", "S", "T"], ["Y", "T"], ["X", "Y"]] ["S", "T"]).toOption.map (·.output) ==
  some ["X", "Y", "S", "T"]
#guard (certifyNodeReference "Root" [["X", "S", "T"], ["Y", "T"], ["X", "Y"]]
    [["S", "T"], ["T"]] ["S", "T"]).toOption.map (·.output) == some ["Root", "X", "Y", "S", "T"]

/-- General completeness, not a result bounded to the examples above. -/
example (trace : Trace lists result) :
    ∃ certificate, mergeReference lists = .ok certificate ∧ certificate.output = result :=
  mergeReference_complete trace
example (lists : List (List String)) :
    (mergeReference lists).toOption.isSome = true ↔ ∃ result, Trace lists result :=
  mergeReference_success_iff
example (graph : Graph) (certificate : GraphCertified graph root) :
    certificate.output.length ≤ graph.nodes.length := certificate.length_bound
#print axioms Trace.length_bound
#print axioms mergeReferenceWithFuel_complete
#print axioms mergeReference_complete
#print axioms mergeReference_success_iff
#print axioms GraphTrace.declared
#print axioms GraphTrace.parent_budget
#print axioms GraphCertified.length_bound
#eval IO.println "REFERENCE-MERGE-OK"
end LeanPoo.Tests.ReferenceMerge
