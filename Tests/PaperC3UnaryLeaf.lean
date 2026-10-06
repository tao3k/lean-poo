import LeanPoo.Prototype.C3GraphSemantics

/-! A parent-edge graph with a shared leaf ancestor. The theorem applies to
all root lists, including repeated roots and a later missing lookup. -/

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3UnaryLeaf

private def graph : C3.Graph :=
  [("A", ["P"]), ("B", ["P"]), ("P", [])]

private theorem valid : C3.validateGraph graph = .ok () := by
  simp [C3.validateGraph, graph, C4.unique, C4.uniqueStep]
  rfl

private theorem unary : C3.UnaryLeafGraph graph := by
  intro root entry lookup
  by_cases ha : root = "A"
  · subst root
    right
    exact ⟨"P", by decide, by decide, by decide⟩
  by_cases hb : root = "B"
  · subst root
    right
    exact ⟨"P", by decide, by decide, by decide⟩
  by_cases hp : root = "P"
  · subst root
    left
    decide
  have ha' : "A" ≠ root := Ne.symm ha
  have hb' : "B" ≠ root := Ne.symm hb
  have hp' : "P" ≠ root := Ne.symm hp
  simp [graph, ha', hb', hp'] at lookup

private theorem every_batch (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached_unary_leaf graph valid unary roots

#guard (C3.linearizeMany graph ["A", "B", "A", "P"]) matches
  .ok [["A", "P"], ["B", "P"], ["A", "P"], ["P"]]
#guard (C3.linearizeMany graph ["A", "B", "Missing"]) matches
  .error (.unknownNode "Missing")

#eval IO.println "POOF-C3-UNARY-LEAF-OK roots=all sharedParent=true repeated=true lateMissing=true"
#print axioms C3.linearizeMany_eq_uncached_unary_leaf
#print axioms every_batch

end LeanPoo.Tests.PaperC3UnaryLeaf
