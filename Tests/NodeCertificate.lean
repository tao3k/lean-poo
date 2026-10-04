import LeanPoo.C4.Linearize

namespace LeanPoo.Tests.NodeCertificate
open C4

private def error? (result : Except Error α) : Option Error :=
  match result with
  | .ok _ => none
  | .error error => some error

#guard (certifyTail [["T"], ["S", "T"], ["T"]] ["S", "T"]).toOption.map (·.output) ==
  some ["S", "T"]
#guard (certifyTail [] []).toOption.map (·.output) == some []
#guard error? (certifyTail [] ["T"]) == some .incompatibleSuffixes
#guard error? (certifyTail [["S", "T"]] ["T"]) == some .incompatibleSuffixes
#guard error? (certifyTail [["A"], ["B"]] ["A"]) == some .incompatibleSuffixes
#guard error? (certifyTail [["T"]] ["X", "T"]) == some .incompatibleSuffixes
#guard error? (certifyTail [["T", "S"], ["S", "T"]] ["S", "T"]) == some .incompatibleSuffixes

private def orders := [["X", "S", "T"], ["Y", "T"], ["X", "Y"]]
private def tails := [["S", "T"], ["T"]]
#guard (certifyNode "Root" orders tails ["S", "T"]).toOption.map (·.output) ==
  some ["Root", "X", "Y", "S", "T"]
#guard (certifyNode "Root" [] [] []).toOption.map (·.output) == some ["Root"]
#guard error? (certifyNode "Root" [["Root"]] [] []) == some (.cycle "Root")
#guard error? (certifyNode "T" [] [["T"]] ["T"]) == some (.cycle "T")
#guard error? (certifyNode "Root" [] [["T", "T"]] ["T", "T"]) == some .inconsistentOrder
#guard error? (certifyNode "Root" [["S", "X", "T"]] tails ["S", "T"]) == some .suffixOrderViolation
#guard error? (certifyNode "Root" [["A", "B"], ["B", "A"]] [] []) == some .inconsistentOrder

example (tails : List (List String)) (first second : TailCertified tails) :
    first.output = second.output := first.unique second
example (tails : List (List String)) (selected : TailCertified tails) (member : tail ∈ tails) :
    tail.length ≤ selected.output.length := selected.longest member
example (orders tails : List (List String)) (certificate : NodeCertified name orders tails) :
    certificate.output.Nodup := certificate.nodup
example (orders tails : List (List String)) (certificate : NodeCertified name orders tails)
    (member : order ∈ orders) :
    order.Sublist certificate.output := certificate.preserves member
example (orders tails : List (List String)) (certificate : NodeCertified name orders tails)
    (member : tail ∈ tails) :
    tail.IsSuffix certificate.output := certificate.parent_suffix member

private def graph : Graph :=
  { nodes := [{ name := "T", suffix := true },
      { name := "S", parentOrders := [["T"]], suffix := true },
      { name := "X", parentOrders := [["S"]] },
      { name := "Y", parentOrders := [["T"]] },
      { name := "Root", parentOrders := [["X", "Y"]] }] }
#guard (linearizeChecked graph "Root").toOption == some ["Root", "X", "Y", "S", "T"]
#guard (linearizeChecked graph "T").toOption == some ["T"]
#print axioms TailCertified.longest
#print axioms TailCertified.comparable
#print axioms TailCertified.unique
#print axioms NodeCertified.preserves
#print axioms NodeCertified.parent_suffix
#print axioms NodeCertified.nodup
#print axioms NodeCertified.head
#print axioms NodeCertified.covers
#eval IO.println "NODE-CERTIFICATE-OK"
end LeanPoo.Tests.NodeCertificate
