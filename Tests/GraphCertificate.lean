import LeanPoo.C4.GraphCertificate

namespace LeanPoo.Tests.GraphCertificate
open C4

private def error? (result : Except Error α) : Option Error :=
  match result with
  | .ok _ => none
  | .error error => some error

private def diamond : Graph :=
  { nodes := [{ name := "Base" },
      { name := "Left", parentOrders := [["Base"]] },
      { name := "Right", parentOrders := [["Base"]] },
      { name := "Root", parentOrders := [["Left", "Right"]] }] }
#guard (linearizeCertified diamond "Root").toOption.map (·.output) ==
  some ["Root", "Left", "Right", "Base"]
#guard (linearizeCertified diamond "Base").toOption.map (·.output) == some ["Base"]

private def suffixes : Graph :=
  { nodes := [{ name := "T", suffix := true },
      { name := "S", parentOrders := [["T"]], suffix := true },
      { name := "X", parentOrders := [["S"]] },
      { name := "Y", parentOrders := [["T"]] },
      { name := "Root", parentOrders := [["X", "Y"]] }] }
#guard (linearizeCertified suffixes "Root").toOption.map (·.output) ==
  some ["Root", "X", "Y", "S", "T"]
private def repeated : Graph :=
  { nodes := [{ name := "Base" }, { name := "Left", parentOrders := [["Base"]] },
      { name := "Right", parentOrders := [["Base"]] },
      { name := "Root", parentOrders := [["Left"], ["Right"], ["Left"]] }] }
#guard (linearizeCertified repeated "Root").toOption.map (·.output) ==
  (linearize repeated "Root").toOption

private def conflict : Graph :=
  { nodes := [{ name := "A" }, { name := "B" },
      { name := "Root", parentOrders := [["A", "B"], ["B", "A"]] }] }
#guard error? (linearizeCertified conflict "Root") == some .inconsistentOrder
#guard error? (linearizeCertified diamond "Missing") == some (.unknownNode "Missing")
private def cycle : Graph :=
  { nodes := [{ name := "A", parentOrders := [["B"]] },
      { name := "B", parentOrders := [["A"]] }] }
#guard error? (linearizeCertified cycle "A") == some (.cycle "A")
private def disconnected : Graph :=
  { nodes := [{ name := "Root" }, { name := "Broken", parentOrders := [["Missing"]] }] }
#guard (linearizeCertified disconnected "Root").toOption.map (·.output) == some ["Root"]

#guard (reconstruct diamond "Root").toOption.map (·.output) ==
  some ["Root", "Left", "Right", "Base"]
#guard (reconstruct suffixes "Root").toOption.map (·.mostSpecificTail) == some ["S", "T"]
#guard (reconstruct suffixes "S").toOption.map (·.mostSpecificTail) == some ["S", "T"]
#guard (reconstruct repeated "Root").toOption.map (·.output) ==
  some ["Root", "Left", "Right", "Base"]
#guard error? (reconstruct conflict "Root") == some .inconsistentOrder
#guard error? (reconstruct cycle "A") == some (.cycle "A")
#guard error? (reconstruct diamond "Missing") == some (.unknownNode "Missing")
#guard (reconstruct disconnected "Root").toOption.map (·.output) == some ["Root"]
private def duplicateDeclarations : Graph :=
  { nodes := [{ name := "Root" }, { name := "Root", parentOrders := [["Missing"]] }] }
#guard (reconstruct duplicateDeclarations "Root").toOption.map (·.output) == some ["Root"]
private def suffixViolation : Graph :=
  { nodes := [{ name := "S", suffix := true }, { name := "X" },
      { name := "Root", parentOrders := [["S", "X"]] }] }
#guard error? (reconstruct suffixViolation "Root") == some .suffixOrderViolation
private def incompatibleTails : Graph :=
  { nodes := [{ name := "A", suffix := true }, { name := "B", suffix := true },
      { name := "Root", parentOrders := [["A", "B"]] }] }
#guard error? (reconstruct incompatibleTails "Root") == some .incompatibleSuffixes

example (trace : GraphTrace graph root output tail) :
    ∃ result, reconstruct graph root = .ok result ∧
      result.output = output ∧ result.mostSpecificTail = tail := reconstruct_complete trace
example (graph : Graph) (root : String) :
    (reconstruct graph root).toOption.isSome = true ↔
      ∃ output tail, GraphTrace graph root output tail := reconstruct_success_iff
example (first : GraphTrace graph root output₁ tail₁)
    (second : GraphTrace graph root output₂ tail₂) : output₁ = output₂ ∧ tail₁ = tail₂ :=
  first.unique second
example (compiled : linearize graph root = .ok output) (trace : GraphTrace graph root output tail) :
    ∃ certificate, linearizeCertified graph root = .ok certificate ∧ certificate.output = output :=
  linearizeCertified_complete compiled trace

example (graph : Graph) (certificate : GraphCertified graph root) :
    linearize graph root = .ok certificate.output := certificate.compiled
example (graph : Graph) (certificate : GraphCertified graph root) :
    certificate.output.Nodup := certificate.nodup
example (graph : Graph) (certificate : GraphCertified graph root) :
    item ∈ certificate.output ↔ Ancestor graph item root := certificate.covers
example (graph : Graph) (certificate : GraphCertified graph root)
    (path : Ancestor graph ancestor root) :
    ∃ order tail, GraphTrace graph ancestor order tail ∧ order.Sublist certificate.output :=
  certificate.ancestor path
example (graph : Graph) (certificate : GraphCertified graph root)
    (path : Ancestor graph ancestor root) (found : graph.findNode? ancestor = some node)
    (flag : node.suffix = true) :
    ∃ order tail, GraphTrace graph ancestor order tail ∧ order.IsSuffix certificate.output :=
  certificate.ancestor_suffix path found flag
#print axioms GraphCertified.nodup
#print axioms GraphCertified.head
#print axioms GraphCertified.covers
#print axioms GraphCertified.ancestor
#print axioms GraphCertified.ancestor_suffix
#print axioms GraphCertified.local_order
#print axioms GraphCertified.unique
#print axioms respectsSuffixTail_complete
#print axioms respectsSuffixTail_iff
#print axioms mergeWithSuffixReference_complete
#print axioms certifyTail_complete
#print axioms certifyNodeReference_complete
#print axioms reconstruct_complete
#print axioms reconstruct_success_iff
#print axioms GraphTrace.unique
#print axioms linearizeCertified_complete
#eval IO.println "GRAPH-CERTIFICATE-OK"
end LeanPoo.Tests.GraphCertificate
