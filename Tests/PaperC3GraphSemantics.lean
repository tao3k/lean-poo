import LeanPoo.Prototype.C3GraphSemantics

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3GraphSemantics

private def graph : C3.Graph :=
  [("O", []), ("A", ["O"]), ("B", ["O"]),
   ("X", ["A", "B"]), ("Y", ["B", "O"])]

private def roots : List String := ["X", "Y", "A", "X"]

#guard (C3.linearizeUncachedMany graph roots).toOption ==
  some [["X", "A", "B", "O"], ["Y", "B", "O"], ["A", "O"],
    ["X", "A", "B", "O"]]
#guard (C3.certifyGraph graph roots).toOption.map (·.orders) ==
  some [["X", "A", "B", "O"], ["Y", "B", "O"], ["A", "O"],
    ["X", "A", "B", "O"]]
#guard C3.certifyGraph [("A", ["B"]), ("B", ["A"])] ["A"] matches
  .error (.cached (.cycle _))
#guard C3.certifyGraph [("A", []), ("A", [])] [] matches
  .error (.cached (.duplicateNode "A"))
#guard C3.linearizeUncached [("A", ["B"]), ("B", ["A"])] "A" matches
  .error (.cycle _)
#guard C3.linearizeUncached [("A", ["missing"])] "A" matches
  .error (.unknownNode "missing")
#guard C3.linearizeUncached [("A", []), ("A", [])] "A" matches
  .error (.duplicateNode "A")
#guard C3.linearizeUncached [("O", []), ("A", ["O"]), ("B", ["O"]),
  ("X", ["A", "B"]), ("Y", ["B", "A"]), ("Z", ["X", "Y"])] "Z" matches
  .error .inconsistentOrder

private theorem admitted_agrees (certificate : C3.GraphCertificate graph roots) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  certificate.agrees

private theorem admitted_first_root (certificate : C3.GraphCertificate graph roots) :
    ∃ order tail, certificate.orders = order :: tail ∧ order.head? = some "X" := by
  obtain ⟨order, tail, rows, trace⟩ := certificate.source_traces.head
  exact ⟨order, tail, rows, trace.root_head⟩

private theorem admitted_first_parent_order (certificate : C3.GraphCertificate graph roots) :
    ∃ (entry : String × List String) (tail : List String)
      (rest : List (List String)),
      graph.find? (fun row => row.1 == "X") = some entry ∧
      certificate.orders = ("X" :: tail) :: rest ∧
      entry.2.Sublist tail ∧ tail.Nodup := by
  obtain ⟨order, rest, rows, trace⟩ := certificate.source_traces.head
  obtain ⟨entry, tail, lookup, same, parents, nodup⟩ := trace.parent_order
  subst order
  exact ⟨entry, tail, rest, lookup, rows, parents, nodup⟩

private theorem source_root_unique (left : C3.GraphTrace graph fuel₁ "X" first)
    (right : C3.GraphTrace graph fuel₂ "X" second) : first = second :=
  left.unique right

private theorem admitted_batch_unique (certificate : C3.GraphCertificate graph roots)
    (other : C3.ParentTraces graph fuel roots orders) :
    certificate.orders = orders :=
  certificate.eq_source other

#eval IO.println "POOF-C3-GRAPH-SEMANTICS-OK singleton=allGraphs recursiveSourceTrace=true cachedBatchAdmission=true"
#print axioms C3.linearizeMany_singleton
#print axioms C3.linearizeUncached_sound
#print axioms C3.linearizeUncachedMany_sound
#print axioms C3.GraphTrace.unique
#print axioms C3.ParentTraces.unique
#print axioms C3.GraphCertificate.source_traces
#print axioms C3.GraphCertificate.eq_source
#print axioms C3.GraphCertificate.order_count
#print axioms C3.GraphCertificate.agrees
#print axioms admitted_first_root
#print axioms admitted_first_parent_order
#print axioms source_root_unique
#print axioms admitted_batch_unique
#print axioms admitted_agrees

end LeanPoo.Tests.PaperC3GraphSemantics
