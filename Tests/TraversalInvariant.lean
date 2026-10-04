import LeanPoo.C4.TraversalInvariant

namespace LeanPoo.Tests.TraversalInvariant
open C4 LinearizeState

private def t : Linearization := ⟨["T"], none, some "T"⟩
private def s : Linearization := ⟨["S", "T"], some "T", some "S"⟩
private def x : Linearization := ⟨["X", "A", "S", "T"], some "S", some "S"⟩
private def chain : Table := ({} : Table).insert "T" t |>.insert "S" s |>.insert "X" x

private theorem chain_entries (found : lookup chain name = some entry) :
    (name = "X" ∧ entry = x) ∨ (name = "S" ∧ entry = s) ∨ (name = "T" ∧ entry = t) := by
  by_cases first : "X" = name
  · subst name
    have same : x = entry := by simpa [chain, lookup_insert] using found
    exact .inl ⟨rfl, same.symm⟩
  · by_cases second : "S" = name
    · subst name
      have same : s = entry := by simpa [chain, lookup_insert] using found
      exact .inr (.inl ⟨rfl, same.symm⟩)
    · by_cases third : "T" = name
      · subst name
        have same : t = entry := by simpa [chain, lookup_insert] using found
        exact .inr (.inr ⟨rfl, same.symm⟩)
      · simp [chain, first, second, third, lookup] at found

private theorem chain_valid : SuffixCacheInvariant chain := by
  constructor
  · intro name entry found
    rcases chain_entries found with ⟨same, actual⟩ | ⟨same, actual⟩ | ⟨same, actual⟩ <;>
      subst name <;> subst entry <;> rfl
  · intro name entry found next link
    rcases chain_entries found with ⟨same, actual⟩ | ⟨same, actual⟩ | ⟨same, actual⟩
    · subst name; subst entry
      have same : "S" = next := Option.some.inj link
      subst next
      exact ⟨s, by simp [chain, lookup_insert], ⟨["A"], rfl⟩⟩
    · subst name; subst entry
      have same : "T" = next := Option.some.inj link
      subst next
      exact ⟨t, by simp [chain, lookup_insert], ⟨[], rfl⟩⟩
    · subst name; subst entry
      cases link

#guard chain.size == 3
#guard suffixReaches chain "X" "T"
#guard suffixReaches chain "X" "S"
#guard suffixReaches chain "S" "T"
#guard suffixReaches chain "T" "T"
#guard !suffixReaches chain "T" "S"
#guard !suffixReaches chain "X" "Missing"
#guard !suffixReachesWithFuel chain "X" "T" 0
#guard !suffixReachesWithFuel chain "X" "T" 2
#guard suffixReachesWithFuel chain "X" "T" 3
#guard suffixReachesWithFuel ({} : Table) "Self" "Self" 1
#guard !suffixReachesWithFuel ({} : Table) "Self" "Other" 1
private def invalidCycle : Table := ({} : Table).insert "A" ⟨["A"], some "A", some "A"⟩
#guard !suffixReaches invalidCycle "A" "Missing"
#guard suffixReaches invalidCycle "A" "A"

private def duplicateGraph : Graph :=
  { nodes := [{ name := "Root" }, { name := "Root", parentOrders := [["Missing"]] }] }
#guard (nodeIndex duplicateGraph).get? "Root" == duplicateGraph.findNode? "Root"
#guard (nodeIndex duplicateGraph).get? "Missing" == none
#guard match linearize duplicateGraph "Root" with
  | .error (.duplicateNode "Root") => true
  | _ => false

example : SuffixCacheInvariant chain := chain_valid
example (graph : Graph) (name : String) : (nodeIndex graph)[name]? = graph.findNode? name :=
  nodeIndex_lookup graph name
example (valid : SuffixCacheInvariant table) :
    suffixReaches table source target = true ↔ ∃ steps, SuffixPath table source target steps :=
  suffixReaches_iff valid
example (path : SuffixPath table source target steps) (valid : SuffixCacheInvariant table) :
    steps ≤ table.size := path.length_bound valid
example (valid : CacheInvariant graph table) (fresh : lookup table name = none)
    (trace : GraphTrace graph name entry.precedence tail)
    (links : ∀ next, entry.inheritedSuffix = some next →
      ∃ child, lookup table next = some child ∧ child.precedence.IsSuffix entry.precedence.tail) :
    CacheInvariant graph (table.insert name entry) := valid.insert fresh trace links
example (valid : CacheInvariant graph table) (found : lookup table source = some entry)
    (accepted : suffixReaches table source target = true) : Ancestor graph target source :=
  (suffixReaches_ancestor valid found accepted).1

#print axioms nodeIndex_lookup
#print axioms nodeIndex_declared
#print axioms suffixReachesWithFuel_sound
#print axioms suffixReachesWithFuel_complete
#print axioms SuffixPath.endpoint
#print axioms SuffixPath.ne
#print axioms SuffixPath.length_bound
#print axioms suffixReaches_sound
#print axioms suffixReaches_complete
#print axioms suffixReaches_iff
#print axioms suffixReaches_preserves
#print axioms CacheInvariant.empty
#print axioms CacheInvariant.insert
#print axioms suffixReaches_ancestor
#eval IO.println "TRAVERSAL-INVARIANT-OK"

end LeanPoo.Tests.TraversalInvariant
