import LeanPoo.C4.Linearize

namespace LeanPoo.Tests.ExtendedPrecedence
open C4 Precedence
private def same (first second : Except Error (List String)) : Bool :=
  match first, second with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

#guard choose [["A"], ["B", "A"]] == some "B"
#guard eligible [["A"], ["B", "A"]] "A" == false
#guard (mergeCertified [["A"], ["B", "A"]]).toOption.map (·.output) == some ["B", "A"]
#guard (mergeCertified [["A", "B"], ["C", "B"]]).toOption.map (·.output) == some ["A", "C", "B"]
#guard (mergeCertified [[], [], []]).toOption.map (·.output) == some []
#guard (mergeCertified [["A", "B"], ["B", "A"]]).toOption.isNone
#guard (check [["A"], ["B", "A"]] ["A", "B"]).isNone
#guard (check [["A"], ["B", "A"]] ["B"]).isNone
#guard (check [["A"], ["B", "A"]] ["B", "A", "A"]).isNone
#guard (check [["A"]] []).isNone
#guard (check [] ["A"]).isNone
#guard (mergeCertified [["A", "B"], ["A", "B"], []]).toOption.map (·.output) == some ["A", "B"]
#guard (mergeCertified [["A", "A"]]).toOption.isNone
#guard (check [["A", "B"], ["A", "B"]] ["A", "B", "B"]).isNone

/-- A suffix is excluded from the tie-break race: its members are kept for
final append rather than preferred as part of X's ordinary ancestry block. -/
private def parents : List (List String) := [["X", "S", "T"], ["Y"]]
private def locals : List (List String) := [["X"], ["Y"]]
#guard (mergePrefix parents locals []).toOption.map (·.output) == some ["X", "S", "T", "Y"]
#guard (mergePrefix parents locals ["X", "S", "T"]).toOption.map (·.output) == some ["Y"]
#guard (check (candidates parents locals ["X", "S", "T"]) ["X", "Y"]).isNone

private def graph (suffix : Bool) : Graph :=
  { nodes := [{ name := "T" }, { name := "S", parentOrders := [["T"]] },
      { name := "X", parentOrders := [["S"]], suffix }, { name := "Y" },
      { name := "Root", parentOrders := [["X"], ["Y"]] }] }
#guard same (linearizeChecked (graph false) "Root") (.ok ["Root", "X", "S", "T", "Y"])
#guard same (linearizeChecked (graph true) "Root") (.ok ["Root", "Y", "X", "S", "T"])
#guard same (linearizeChecked (graph false) "Root") (linearize (graph false) "Root")
#guard same (linearizeChecked (graph true) "Root") (linearize (graph true) "Root")

private def diamond : Graph :=
  { nodes := [{ name := "Base" },
      { name := "Left", parentOrders := [["Base"]] },
      { name := "Right", parentOrders := [["Base"]] },
      { name := "Child", parentOrders := [["Left", "Right"]] }] }
#guard same (linearizeChecked diamond "Child") (.ok ["Child", "Left", "Right", "Base"])
private def conflict : Graph :=
  { nodes := [{ name := "A" }, { name := "B" },
      { name := "Root", parentOrders := [["A", "B"], ["B", "A"]] }] }
#guard same (linearizeChecked conflict "Root") (.error .inconsistentOrder)
#guard same (linearizeChecked conflict "Missing") (.error (.unknownNode "Missing"))
private def cycle : Graph :=
  { nodes := [{ name := "A", parentOrders := [["B"]] }, { name := "B", parentOrders := [["A"]] }] }
#guard same (linearizeChecked cycle "A") (.error (.cycle "A"))
private def suffixes : Graph :=
  { nodes := [{ name := "A", suffix := true }, { name := "B", suffix := true },
      { name := "Root", parentOrders := [["A"], ["B"]] }] }
#guard same (linearizeChecked suffixes "Root") (.error .incompatibleSuffixes)

/-- Certificates for identical inputs cannot disagree about their outputs. -/
example (first second : Certified lists) : first.output = second.output :=
  first.trace.unique second.trace

/-- The certificate supplies the paper's ordered-subset consistency property
for any parent or local-order candidate, without a graph-size restriction. -/
example (certificate : Certified lists) (present : order ∈ lists) :
    order.Sublist certificate.output := certificate.trace.preserves present

example (certificate : Certified lists) :
    name ∈ certificate.output ↔ ∃ order ∈ lists, name ∈ order := certificate.trace.covers

example (certificate : Certified lists) : certificate.output.Nodup := certificate.trace.nodup
#print axioms choose_eligible
#print axioms choose_leftmost
#print axioms Trace.unique
#print axioms candidates_without_suffix
#print axioms Trace.preserves
#print axioms Trace.covers
#print axioms Trace.nodup
#eval IO.println "EXTENDED-PRECEDENCE-OK"
end LeanPoo.Tests.ExtendedPrecedence
