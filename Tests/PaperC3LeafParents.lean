import LeanPoo.Prototype.C3GraphSemantics

/-! Four leaf parents, reused in opposite order by another root. The graph
premise proves equality for every root list, including late failures. -/

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3LeafParents

private def graph : C3.Graph :=
  [("A", ["P", "Q", "R", "S"]), ("B", ["S", "R", "Q", "P"]),
   ("P", []), ("Q", []), ("R", []), ("S", [])]

private theorem valid : C3.validateGraph graph = .ok () := by
  simp [C3.validateGraph, graph, C4.unique, C4.uniqueStep]
  rfl

private theorem bounded : C3.LeafParentGraph graph := by
  intro root entry lookup
  by_cases ha : root = "A"
  · subst root
    refine ⟨["P", "Q", "R", "S"], by decide, by decide, by decide, ?_⟩
    intro parent member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  by_cases hb : root = "B"
  · subst root
    refine ⟨["S", "R", "Q", "P"], by decide, by decide, by decide, ?_⟩
    intro parent member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  by_cases hp : root = "P"
  · subst root
    exact ⟨[], by decide, by simp, by simp, by simp⟩
  by_cases hq : root = "Q"
  · subst root
    exact ⟨[], by decide, by simp, by simp, by simp⟩
  by_cases hr : root = "R"
  · subst root
    exact ⟨[], by decide, by simp, by simp, by simp⟩
  by_cases hs : root = "S"
  · subst root
    exact ⟨[], by decide, by simp, by simp, by simp⟩
  have ha' : "A" ≠ root := Ne.symm ha
  have hb' : "B" ≠ root := Ne.symm hb
  have hp' : "P" ≠ root := Ne.symm hp
  have hq' : "Q" ≠ root := Ne.symm hq
  have hr' : "R" ≠ root := Ne.symm hr
  have hs' : "S" ≠ root := Ne.symm hs
  simp [graph, ha', hb', hp', hq', hr', hs'] at lookup

private theorem every_batch (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached_leafParents graph valid bounded roots

#guard (C3.linearizeMany graph ["A", "B", "A", "P"]) matches
  .ok [["A", "P", "Q", "R", "S"], ["B", "S", "R", "Q", "P"],
    ["A", "P", "Q", "R", "S"], ["P"]]
#guard (C3.linearizeMany graph ["B", "A", "Missing"]) matches
  .error (.unknownNode "Missing")

#eval IO.println "POOF-C3-LEAF-PARENTS-OK roots=all parents=4 shared=true oppositeOrders=true lateMissing=true"
#print axioms C3.linearizeMany_eq_uncached_leafParents
#print axioms every_batch

end LeanPoo.Tests.PaperC3LeafParents
