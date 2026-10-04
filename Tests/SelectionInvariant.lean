import LeanPoo.C4.SelectionInvariant

namespace LeanPoo.Tests.SelectionInvariant
open C4 LinearizeState

private def sameResult [BEq α] (left right : Except Error α) : Bool :=
  match left, right with
  | .ok first, .ok second => first == second
  | .error first, .error second => first == second
  | _, _ => false

private def chain : Table := ({} : Table)
  |>.insert "T" ⟨["T"], none, some "T"⟩
  |>.insert "S" ⟨["S", "T"], some "T", some "S"⟩
  |>.insert "X" ⟨["X", "S", "T"], some "S", some "S"⟩
  |>.insert "U" ⟨["U"], none, some "U"⟩

#guard sameResult (selectSuffix chain [none, some "T", some "S", none, some "T"] none) (.ok (some "S"))
#guard sameResult (selectSuffix chain [some "S", some "T"] none) (.ok (some "S"))
#guard sameResult (selectSuffix chain [some "T", some "S"] none) (.ok (some "S"))
#guard sameResult (selectSuffix chain [some "S", some "U"] none) (.error .incompatibleSuffixes)
#guard sameResult (selectSuffix chain [some "U", some "S"] none) (.error .incompatibleSuffixes)
#guard sameResult (selectSuffix chain [none, none] none) (.ok none)
#guard suffixTails chain [none, some "T", some "S", some "T"] == [["T"], ["S", "T"], ["T"]]

example (certificate : SuffixCertified orders tail) (unique : tail.Nodup) :
    ∃ result, mergeWithSuffixCertified orders tail = .ok result ∧
      result.output = certificate.output := mergeWithSuffixCertified_complete certificate unique
example (certificate : NodeCertified name orders tails) :
    ∃ result, certifyNode name orders tails certificate.selection.output = .ok result ∧
      result.output = certificate.output ∧ result.selection.output = certificate.selection.output :=
  certifyNode_complete certificate
example (success : selectSuffix table sources initial = .ok chosen) :
    (chosen = initial ∨ chosen ∈ sources) ∧
      ∀ source ∈ initial :: sources, SuffixDominates table chosen source := selectSuffix_sound success
example (valid : SuffixCacheInvariant table)
    (comparable : ∀ left ∈ initial :: sources, ∀ right ∈ initial :: sources,
      SuffixDominates table left right ∨ SuffixDominates table right left) :
    ∃ chosen, selectSuffix table sources initial = .ok chosen := selectSuffix_complete valid comparable
example (valid : SuffixCacheInvariant table)
    (success : selectSuffix table sources none = .ok chosen)
    (available : ∀ name, chosen = some name → ∃ entry, lookup table name = some entry) :
    ∃ certificate : TailCertified (suffixTails table sources),
      certificate.output = selectedTail table chosen := selectSuffix_tailCertified valid success available

private def graph : Graph :=
  { nodes := [{ name := "T", suffix := true },
      { name := "S", parentOrders := [["T"]], suffix := true },
      { name := "X", parentOrders := [["S"]] },
      { name := "Y", parentOrders := [["T"]] },
      { name := "Root", parentOrders := [[], ["X", "Y"], ["X"], []] }] }
#guard (linearize graph "Root").toOption == some ["Root", "X", "Y", "S", "T"]
#guard sameResult (linearizeChecked graph "Root") (linearize graph "Root")

#print axioms mergeWithSuffixCertified_complete
#print axioms certifyNode_complete
#print axioms SuffixDominates.refl
#print axioms SuffixDominates.trans
#print axioms selectSuffixStep_sound
#print axioms selectSuffix_sound
#print axioms selectSuffixStep_complete
#print axioms selectSuffix_complete
#print axioms selectSuffix_preserves
#print axioms selectSuffix_tailCertified

/- Retain the original imperative loop as an executable regression oracle
for the extracted runtime operation, including exact error payloads. -/
private def originalSelection (table : Table) (sources : List (Option String))
    (initial : Option String) : Except Error (Option String) := do
  let mut current := initial
  for next in sources do
    match current, next with
    | none, next => current := next
    | _, none => pure ()
    | some before, some after =>
      if suffixReaches table before after then pure ()
      else if suffixReaches table after before then current := some after
      else throw .incompatibleSuffixes
  return current

private def alphabet : List (Option String) :=
  [none, some "T", some "S", some "U", some "Missing"]
private def words : Nat → List (List (Option String))
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun rest => alphabet.map (· :: rest)

#eval do
  let families := (List.range 5).flatMap words
  for sources in families do
    for initial in alphabet do
      unless sameResult (selectSuffix chain sources initial) (originalSelection chain sources initial) do
        throw (IO.userError s!"suffix selection mismatch: {repr sources}, {repr initial}")
  IO.println s!"SELECTION-INVARIANT-OK comparisons={families.length * alphabet.length}"

end LeanPoo.Tests.SelectionInvariant
