import LeanPoo.Prototype.C3GraphSemantics

/-! Two roots share both leaf ancestors but declare them in opposite orders.
The theorem handles every requested root list and the resulting cache hits. -/

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3TwoLeaf

private def graph : C3.Graph :=
  [("A", ["P", "Q"]), ("B", ["Q", "P"]), ("P", []), ("Q", [])]

private theorem valid : C3.validateGraph graph = .ok () := by
  simp [C3.validateGraph, graph, C4.unique, C4.uniqueStep]
  rfl

private theorem bounded : C3.AtMostTwoLeafGraph graph := by
  intro root entry lookup
  by_cases ha : root = "A"
  · subst root
    right
    exact ⟨"P", "Q", by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  by_cases hb : root = "B"
  · subst root
    right
    exact ⟨"Q", "P", by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  by_cases hp : root = "P"
  · subst root
    left
    left
    decide
  by_cases hq : root = "Q"
  · subst root
    left
    left
    decide
  have ha' : "A" ≠ root := Ne.symm ha
  have hb' : "B" ≠ root := Ne.symm hb
  have hp' : "P" ≠ root := Ne.symm hp
  have hq' : "Q" ≠ root := Ne.symm hq
  simp [graph, ha', hb', hp', hq'] at lookup

private theorem every_batch (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached_atMostTwoLeaf graph valid bounded roots

#guard (C3.linearizeMany graph ["A", "B", "A", "Q"]) matches
  .ok [["A", "P", "Q"], ["B", "Q", "P"], ["A", "P", "Q"], ["Q"]]
#guard (C3.linearizeMany graph ["B", "A", "Missing"]) matches
  .error (.unknownNode "Missing")

#eval IO.println "POOF-C3-TWO-LEAF-OK roots=all shared=true oppositeOrders=true lateMissing=true"
#print axioms C3.linearizeMany_eq_uncached_atMostTwoLeaf
#print axioms every_batch

end LeanPoo.Tests.PaperC3TwoLeaf
