import LeanPoo.C4.Linearize

namespace LeanPoo.Tests.SuffixConsistency
open C4

private def output (orders : List (List String)) (tail : List String) :=
  (mergeWithSuffixCertified orders tail).toOption.map (·.output)

#guard respectsSuffixTail ["X", "S", "T"] ["S", "T"]
#guard respectsSuffixTail ["X", "T"] ["S", "T"]
#guard !respectsSuffixTail ["S", "X", "T"] ["S", "T"]
#guard !respectsSuffixTail ["T", "S"] ["S", "T"]
#guard !respectsSuffixTail ["S", "S"] ["S", "T"]
#guard output [["X", "S", "T"], ["Y", "T"], ["X", "Y"]] ["S", "T"] ==
  some ["X", "Y", "S", "T"]
#guard output [["X", "T"], ["S", "T"]] ["S", "T"] == some ["X", "S", "T"]
#guard output [[], ["S", "T"]] ["S", "T"] == some ["S", "T"]
#guard output [["A"], ["B", "A"]] [] == some ["B", "A"]
#guard output [["A", "B"], ["B", "A"]] [] == none
#guard output [["S", "X", "T"]] ["S", "T"] == none
#guard output [["T", "S"]] ["S", "T"] == none

/-- The complete candidate, including its suffix members, is preserved. -/
example (certificate : SuffixCertified orders tail) (member : order ∈ orders) :
    order.Sublist certificate.output := certificate.preserves member
example (certificate : SuffixCertified orders tail) :
    tail.IsSuffix certificate.output := certificate.suffix
example (certificate : SuffixCertified orders tail) (unique : tail.Nodup) :
    certificate.output.Nodup := certificate.nodup unique
example (certificate : SuffixCertified orders tail) :
    name ∈ certificate.output ↔ (∃ order ∈ orders, name ∈ order) ∨ name ∈ tail := certificate.covers

/-- Both ancestors share T, but only S requires suffix ancestry. -/
private def graph : Graph :=
  { nodes := [{ name := "T", suffix := true },
      { name := "S", parentOrders := [["T"]], suffix := true },
      { name := "X", parentOrders := [["S"]] },
      { name := "Y", parentOrders := [["T"]] },
      { name := "Root", parentOrders := [["X", "Y"]] }] }
#guard (linearizeChecked graph "Root").toOption == some ["Root", "X", "Y", "S", "T"]
#guard (linearizeChecked graph "Root").toOption == (linearize graph "Root").toOption
#print axioms respectsSuffixTail_sound
#print axioms append_preserves
#print axioms SuffixCertified.preserves
#print axioms SuffixCertified.suffix
#print axioms SuffixCertified.covers
#print axioms SuffixCertified.nodup
#eval IO.println "SUFFIX-CONSISTENCY-OK"
end LeanPoo.Tests.SuffixConsistency
