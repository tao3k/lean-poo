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

private theorem admitted_agrees (certificate : C3.GraphCertificate graph roots) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  certificate.agrees

#eval IO.println "POOF-C3-GRAPH-SEMANTICS-OK singleton=allGraphs uncachedReference=true cachedBatchAdmission=true"
#print axioms C3.linearizeMany_singleton
#print axioms C3.GraphCertificate.order_count
#print axioms C3.GraphCertificate.agrees
#print axioms admitted_agrees

end LeanPoo.Tests.PaperC3GraphSemantics
