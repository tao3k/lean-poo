import LeanPoo.Prototype.C3GraphSemantics

/-! A concrete no-parent paper graph exercises complete cached/uncached
outcome equality after cache hits and after a later missing root. -/

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3BatchCoherence

private def graph : C3.Graph :=
  [("A", []), ("B", []), ("C", [])]

private theorem valid : C3.validateGraph graph = .ok () := by
  simp [C3.validateGraph, graph, C4.unique]
  rfl

private theorem flat : C3.FlatGraph graph := by
  apply C3.FlatGraph.of_members
  intro entry member
  simp [graph] at member
  rcases member with h | h | h <;> cases h <;> rfl

private theorem every_batch (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached_flat graph valid flat roots

#guard (C3.linearizeMany graph ["A", "B", "A"]) matches
  .ok [["A"], ["B"], ["A"]]
#guard (C3.linearizeMany graph ["A", "Missing"]) matches
  .error (.unknownNode "Missing")
#guard (C3.linearizeUncachedMany graph ["A", "Missing"]) matches
  .error (.unknownNode "Missing")

#eval IO.println "POOF-C3-BATCH-COHERENCE-OK roots=all flat=true repeated=true lateMissing=true"
#print axioms C3.linearizeMany_eq_uncached_of_visit_coherence
#print axioms C3.linearizeMany_eq_uncached_flat
#print axioms every_batch

end LeanPoo.Tests.PaperC3BatchCoherence
