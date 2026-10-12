import LeanPoo.Prototype.C3DAG

open LeanPoo.Prototype
namespace LeanPoo.Tests.C3DAG

private def graph : C3.Graph :=
  [("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["O"]),
   ("D", ["O"]), ("E", ["O"]), ("K1", ["A", "B", "C"]),
   ("K2", ["D", "B", "E"]), ("K3", ["D", "A"]),
   ("Z", ["K1", "K2", "K3"])]

private def ranks : List (String × Nat) :=
  [("O", 1), ("A", 2), ("B", 2), ("C", 2), ("D", 2),
   ("E", 2), ("K1", 3), ("K2", 3), ("K3", 3), ("Z", 4)]

private def dag : C3.DAG graph :=
  (C3.certifyDAG graph ranks).toOption.get (by decide)

private theorem every_batch (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached_dag graph dag roots

#guard (C3.inferDAG graph).isOk
#guard !(C3.certifyDAG graph [("O", 99)]).isOk
#guard !(C3.certifyDAG graph []).isOk
#guard !(C3.inferDAG [("A", ["B"]), ("B", ["A"])]).isOk
#guard (C3.linearizeMany graph ["Z", "K1", "Z", "O"]) matches
  .ok [["Z", "K1", "K2", "K3", "D", "A", "B", "C", "E", "O"],
    ["K1", "A", "B", "C", "O"],
    ["Z", "K1", "K2", "K3", "D", "A", "B", "C", "E", "O"], ["O"]]
#guard (C3.linearizeMany graph ["Z", "K2", "Missing"]) matches
  .error (.unknownNode "Missing")

-- This DAG has contradictory inherited orders. Acyclicity does not imply C3 success.
private def inconsistent : C3.Graph :=
  [("X", []), ("Y", []), ("A", ["X", "Y"]),
   ("B", ["Y", "X"]), ("Z", ["A", "B"])]
#guard (C3.inferDAG inconsistent).isOk
#guard (C3.linearizeMany inconsistent ["A", "B", "Z"]) matches .error (.inconsistentOrder)
example : C3.linearizeMany inconsistent ["A", "B", "Z"] =
  C3.linearizeUncachedMany inconsistent ["A", "B", "Z"]
  := C3.linearizeMany_eq_uncached_dag inconsistent
    ((C3.inferDAG inconsistent).toOption.get (by decide)) _
#guard (C3.inferDAG [("A", ["Missing"])]).isOk
example : C3.linearizeMany [("A", ["Missing"])] ["A"] =
  C3.linearizeUncachedMany [("A", ["Missing"])] ["A"]
  := C3.linearizeMany_eq_uncached_dag _
    ((C3.inferDAG [("A", ["Missing"])]).toOption.get (by decide)) _

private def chain (length : Nat) : C3.Graph :=
  (List.range length).map fun index =>
    (toString index, if index == 0 then [] else [toString (index - 1)])

#guard (C3.inferDAG (chain 40)).isOk
#guard (C3.linearizeMany (chain 40) ["39", "12", "39", "20"]).toOption ==
  (C3.linearizeUncachedMany (chain 40) ["39", "12", "39", "20"]).toOption

#eval IO.println "POOF-C3-DAG-OK roots=all depth=arbitrary shared=true errors=exact chain=40"
#print axioms C3.linearizeMany_eq_uncached_dag
#print axioms every_batch
end LeanPoo.Tests.C3DAG
