import LeanPoo.C4.ComputeInvariant

namespace LeanPoo.Tests.ComputeInvariant
open C4 LinearizeState

example (certificate : TailCertified tails) :
    ∃ normalized : TailCertified (tails.filter (fun tail => !tail.isEmpty)),
      normalized.output = certificate.output := certificate.drop_empty
example (certificate : NodeCertified name orders tails) :
    ∃ normalized : NodeCertified name orders (tails.filter (fun tail => !tail.isEmpty)),
      normalized.output = certificate.output ∧
        normalized.selection.output = certificate.selection.output := certificate.drop_empty
example (valid : SuffixCacheInvariant table)
    (available : ∀ name, some name ∈ sources → ∃ entry, lookup table name = some entry) :
    suffixTails table sources = (sources.map (selectedTail table)).filter (fun tail => !tail.isEmpty) :=
  suffixTails_drop_empty valid available
example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries)
    (certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix)))) (checked : Bool) :
    ∃ chosen, selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen ∧
      computeNode table node checked = .ok {
        precedence := certificate.output
        inheritedSuffix := chosen
        mostSpecificSuffix := if node.suffix then some node.name else chosen } ∧
      selectedTail table chosen = certificate.selection.output :=
  computeNode_certified valid trace found collected certificate checked

private def cache : Table := ({} : Table)
  |>.insert "T" ⟨["T"], none, some "T"⟩
  |>.insert "S" ⟨["S", "T"], some "T", some "S"⟩
  |>.insert "X" ⟨["X", "S", "T"], some "S", some "S"⟩
  |>.insert "Y" ⟨["Y", "T"], some "T", some "T"⟩
private def root : Node := { name := "Root", parentOrders := [[], ["X", "Y"], ["X"], []] }
#guard (computeNode cache root false).toOption.map (·.precedence) == some ["Root", "X", "Y", "S", "T"]
#guard (computeNode cache root true).toOption == (computeNode cache root false).toOption
#guard (computeNode cache root true).toOption.map (·.inheritedSuffix) == some (some "S")
#guard (computeNode cache root true).toOption.map (·.mostSpecificSuffix) == some (some "S")
#guard (computeNode cache { root with suffix := true } true).toOption.map (·.mostSpecificSuffix) == some (some "Root")
#guard (computeNode ({} : Table) { name := "Fresh" } true).toOption.map (·.precedence) == some ["Fresh"]
#guard match computeNode cache { name := "Root", parentOrders := [["Missing"]] } false with
  | .error (.unknownNode name) => name == "Missing"
  | _ => false
#guard match readSuffix cache (some "Missing") with
  | .error (.unknownNode name) => name == "Missing"
  | _ => false
#guard (readSuffix cache none).toOption == some []
#guard (collectSuffixTails cache [none, some "T", some "S", none, some "T"]).toOption ==
  some [["T"], ["S", "T"], ["T"]]
#guard (certifyNode "Fresh" [] [] []).toOption.map (·.output) ==
  (certifyNode "Fresh" [] [[], []] []).toOption.map (·.output)

#print axioms TailCertified.drop_empty
#print axioms NodeCertified.drop_empty
#print axioms readSuffix_complete
#print axioms collectSuffixTails_complete
#print axioms computeNode_complete
#print axioms collected_suffix_available
#print axioms suffixTails_drop_empty
#print axioms computeNode_certified
#print axioms computeNode_insert_preserves

/- Original imperative checker collection as an executable refactor oracle,
including absent metadata, repeated tails, and exact missing-name errors. -/
private def originalTails (table : Table) (sources : List (Option String)) :
    Except Error (List (List String)) := do
  let mut reversed := []
  for source in sources do
    if let some name := source then
      let some cached := lookup table name | throw (.unknownNode name)
      reversed := cached.precedence :: reversed
  return reversed.reverse
private def sameResult [BEq α] (first second : Except Error α) : Bool :=
  match first, second with
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false
private def words : Nat → List (List (Option String))
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest =>
    [none, some "T", some "S", some "Missing1", some "Missing2"].map (· :: rest)
#eval do
  let families : List (List (Option String)) := (List.range 5).flatMap words
  for sources in families do
    unless sameResult (collectSuffixTails cache sources) (originalTails cache sources) do
      throw (IO.userError s!"suffix collector mismatch: {repr sources}")
  IO.println s!"COMPUTE-INVARIANT-OK families={families.length}"

end LeanPoo.Tests.ComputeInvariant
