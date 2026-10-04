import LeanPoo.C4.NormalizationInvariant

namespace LeanPoo.Tests.NormalizationInvariant
open C4 MergeState Precedence

#guard (merge [["B"], ["A"], ["B"], []]).toOption == some ["B", "A"]
#guard (merge [["A", "A"], ["A", "A"], []]).toOption.isNone
#guard (merge [["A", "B"], [], ["B", "A"], ["A", "B"]]).toOption.isNone
#guard (merge [[], [], []]).toOption == some []

example (same : ScanEquivalent left right) : choose left = choose right := choose_scan same
example (same : ScanEquivalent left right) : Trace left output ↔ Trace right output := trace_scan same
example (names : List String) (order : String → List String) (locals : List (List String)) :
    (merge (names.map order ++ locals)).toOption =
      (merge ((unique names).map order ++ locals)).toOption := merge_unique_parents names order locals
example (names : List String) (order : String → List String) (locals : List (List String))
    (tail : List String) :
    Trace (candidates (names.map order) locals tail) output ↔
      Trace (candidates ((unique names).map order) (pending locals) tail) output :=
  trace_normalized_candidates names order locals tail
example (certificate : NodeCertified name (names.map order ++ locals) (names.map parentTail)) :
    ∃ normalized : NodeCertified name ((unique names).map order ++ pending locals)
        ((unique names).map parentTail),
      normalized.output = certificate.output ∧
        normalized.selection.output = certificate.selection.output := nodeCertificate_normalize certificate

example (success : LinearizeState.collectParents table (LinearizeState.parents node) = .ok entries)
    (tail : List String) :
    (merge (entries.map (fun entry => withoutTail entry.precedence tail) ++
      (pending node.parentOrders).map (fun order => withoutTail order tail))).toOption =
    (merge (candidates (node.parentOrders.flatten.map (LinearizeState.cachedOrder table))
      node.parentOrders tail)).toOption := LinearizeState.collected_candidates_normalize success tail

#print axioms ScanEquivalent.refl
#print axioms ScanEquivalent.trans
#print axioms ScanEquivalent.map
#print axioms ScanEquivalent.append
#print axioms ScanEquivalent.duplicate
#print axioms unique_scan
#print axioms choose_scan
#print axioms trace_scan
#print axioms merge_trace_congr
#print axioms merge_scan
#print axioms merge_pending
#print axioms merge_unique_parents
#print axioms merge_empty_locals
#print axioms merge_normalized_candidates
#print axioms trace_normalized_candidates
#print axioms nodeCertificate_normalize
#print axioms LinearizeState.collected_precedence_map
#print axioms LinearizeState.collected_candidates_normalize

private def parentOrder (name : String) : List String :=
  if name == "B" then ["B", "T"]
  else if name == "D" then ["T", "A"]
  else ["A", "T"]
private def names : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => (names n).flatMap fun rest => ["A", "B", "C", "D"].map (· :: rest)
private def localOrders : Nat → List (List (List String))
  | 0 => [[]]
  | n + 1 => (localOrders n).flatMap fun rest =>
    [[], ["A"], ["B"], ["A", "B"], ["B", "A"], ["T"], ["T", "A"]].map (· :: rest)

/- Finite regression supplements the generic proofs. C and A intentionally
have identical full parent orders; tail cleanup can introduce further equality. -/
#eval do
  let parentFamilies : List (List String) := (List.range 4).flatMap names
  let locals : List (List (List String)) := (List.range 3).flatMap localOrders
  let tails : List (List String) := [[], ["T"], ["A", "T"]]
  let mut count := 0
  for parents in parentFamilies do
    for orders in locals do
      for tail in tails do
        let original := (merge (candidates (List.map parentOrder parents) orders tail)).toOption
        let normalized := (merge (candidates ((unique parents).map parentOrder) (pending orders) tail)).toOption
        unless original == normalized do
          throw (IO.userError s!"normalization mismatch: {repr parents}, {repr orders}, {repr tail}")
        count := count + 1
    if count % 1710 == 0 then IO.println s!"NORMALIZATION-PROGRESS comparisons={count}"
  IO.println s!"NORMALIZATION-INVARIANT-OK comparisons={count}"

end LeanPoo.Tests.NormalizationInvariant
