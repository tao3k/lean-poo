import LeanPoo.C4.NormalizationInvariant

namespace LeanPoo.C4

/-- Every nonempty graph-derived most-specific tail is the complete
precedence of an actually declared suffix ancestor. -/
theorem GraphTrace.tail_origin (trace : GraphTrace graph root output tail) :
    tail = [] ∨ ∃ name node, graph.findNode? name = some node ∧ node.suffix = true ∧
      Ancestor graph name root ∧ GraphTrace graph name tail tail := by
  induction trace with
  | @node root node found rows names parents certificate ih =>
    by_cases marked : node.suffix = true
    · refine .inr ⟨root, node, found, marked, .self, ?_⟩
      simpa [marked] using GraphTrace.node found rows names parents certificate
    · simp only [marked]
      rcases certificate.selection.chosen with ⟨_, empty⟩ | member
      · exact .inl empty
      · obtain ⟨row, present, same⟩ := List.mem_map.mp member
        rcases ih row present with empty | ⟨name, declaration, declared, flag, earlier, derivation⟩
        · exact .inl (same ▸ empty)
        · refine .inr ⟨name, declaration, declared, flag, ?_, ?_⟩
          · apply Ancestor.parent found
            · rw [← names]; exact List.mem_map.mpr ⟨row, present, rfl⟩
            · exact earlier
          · simpa [same] using derivation

/-- An empty graph-derived tail means there is no declared suffix ancestor. -/
theorem GraphTrace.tail_empty_iff (trace : GraphTrace graph root output tail) :
    tail = [] ↔ ∀ target node, graph.findNode? target = some node → node.suffix = true →
      ¬ Ancestor graph target root := by
  constructor
  · intro empty target node found marked ancestor
    obtain ⟨ancestorOutput, ancestorTail, derived, kept⟩ := trace.ancestor_tail ancestor
    have whole := derived.flagged found marked
    rw [whole, empty] at kept
    have impossible : ancestorOutput = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero kept.length_le)
    have present := derived.root_mem
    simp [impossible] at present
  · intro absent
    rcases trace.tail_origin with empty | ⟨target, node, found, marked, ancestor, _⟩
    · exact empty
    · exact False.elim (absent target node found marked ancestor)

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

/-- Strong metadata premises needed for complete inherited-suffix walks.
Coverage is a semantic graph obligation, not an assumed pointer-path result.
Population of these premises by computeNode remains a separate proof. -/
structure MetadataInvariant (graph : Graph) (table : Table) : Prop extends CacheInvariant graph table where
  tail : ∀ name entry, lookup table name = some entry →
    GraphTrace graph name entry.precedence (selectedTail table entry.mostSpecificSuffix)
  selected : ∀ name entry, lookup table name = some entry → ∀ suffix,
    entry.mostSpecificSuffix = some suffix → ∃ child, lookup table suffix = some child
  coverage : ∀ name entry, lookup table name = some entry → ∀ target node,
    graph.findNode? target = some node → node.suffix = true → Ancestor graph target name →
    target ≠ name → ∃ next child, entry.inheritedSuffix = some next ∧
      lookup table next = some child ∧ target ∈ child.precedence

theorem MetadataInvariant.empty (graph : Graph) : MetadataInvariant graph ({} : Table) := by
  refine ⟨CacheInvariant.empty graph, ?_, ?_, ?_⟩ <;>
    intro name entry found <;> simp [lookup] at found

/-- Graph tail origin proves that a cached selected name is a declared
suffix node; this fact is derived rather than assumed by the invariant. -/
theorem selected_suffix_declared (valid : MetadataInvariant graph table)
    (found : lookup table name = some entry) (selected : entry.mostSpecificSuffix = some suffix) :
    ∃ child node, lookup table suffix = some child ∧ graph.findNode? suffix = some node ∧ node.suffix = true := by
  obtain ⟨child, cached⟩ := valid.selected name entry found suffix selected
  have derivation : GraphTrace graph name entry.precedence child.precedence := by
    simpa [selectedTail, selected, cached] using valid.tail name entry found
  rcases derivation.tail_origin with empty | ⟨origin, node, declared, marked, _, originTrace⟩
  · have head := valid.suffixes.head suffix child cached
    simp [empty] at head
  · have same : origin = suffix := Option.some.inj
      (originTrace.head.symm.trans (valid.suffixes.head suffix child cached))
    subst origin
    exact ⟨child, node, cached, declared, marked⟩


/-- Canonical metadata has no selected suffix exactly when the graph has no
marked ancestor, including the cached node itself. -/
theorem metadata_none_iff (valid : MetadataInvariant graph table)
    (found : lookup table name = some entry) :
    entry.mostSpecificSuffix = none ↔ ∀ target node,
      graph.findNode? target = some node → node.suffix = true → ¬ Ancestor graph target name := by
  have trace := valid.tail name entry found
  constructor
  · intro absent
    apply trace.tail_empty_iff.mp
    simp [selectedTail, absent]
  · intro absent
    have empty := trace.tail_empty_iff.mpr absent
    cases selected : entry.mostSpecificSuffix with
    | none => rfl
    | some suffix =>
      obtain ⟨child, cached⟩ := valid.selected name entry found suffix selected
      have noPrecedence : child.precedence = [] := by
        simpa [selectedTail, selected, cached] using empty
      have head := valid.suffixes.head suffix child cached
      simp [noPrecedence] at head

/-- A selected suffix name is an actual marked graph ancestor of the cached node. -/
theorem metadata_selected_ancestor (valid : MetadataInvariant graph table)
    (found : lookup table name = some entry) (selected : entry.mostSpecificSuffix = some suffix) :
    Ancestor graph suffix name := by
  obtain ⟨child, _, cached, _, _⟩ := selected_suffix_declared valid found selected
  have trace := valid.tail name entry found
  have kept : child.precedence.IsSuffix entry.precedence := by
    simpa [selectedTail, selected, cached] using trace.suffix
  exact trace.covers.mp (kept.sublist.subset ((valid.tail suffix child cached).root_mem))

/-- Every declared suffix ancestor is reached by the inherited-suffix walk
under semantic coverage; strict cached precedence decrease proves termination. -/
theorem flagged_ancestor_path (valid : MetadataInvariant graph table)
    (found : lookup table source = some entry) (declared : graph.findNode? target = some node)
    (marked : node.suffix = true) (ancestor : Ancestor graph target source) :
    ∃ steps, SuffixPath table source target steps := by
  have bounded : ∀ budget source entry, entry.precedence.length ≤ budget →
      lookup table source = some entry → Ancestor graph target source →
      ∃ steps, SuffixPath table source target steps := by
    intro budget
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
      intro source entry bound found ancestor
      by_cases same : target = source
      · subst target; exact ⟨0, .here⟩
      · obtain ⟨next, child, link, cached, contains⟩ :=
          valid.coverage source entry found target node declared marked ancestor same
        have one : SuffixPath table source next 1 := .next found link .here
        obtain ⟨last, lastFound, _, shorter⟩ := one.endpoint valid.suffixes found
        have actual : last = child := Option.some.inj (lastFound.symm.trans cached)
        subst last
        have smaller : child.precedence.length < budget :=
          Nat.lt_of_lt_of_le (shorter (by decide)) bound
        obtain ⟨tail, derivation⟩ := valid.derived next child cached
        obtain ⟨steps, rest⟩ := ih child.precedence.length smaller next child (Nat.le_refl _)
          cached (derivation.covers.mp contains)
        exact ⟨steps + 1, .next found link rest⟩
  exact bounded entry.precedence.length source entry (Nat.le_refl _) found ancestor

/-- With graph-backed coverage, the actual table-size walk recognizes exactly
the ancestry relation for declared suffix targets. -/
theorem suffixReaches_flagged_iff (valid : MetadataInvariant graph table)
    (found : lookup table source = some entry) (declared : graph.findNode? target = some node)
    (marked : node.suffix = true) :
    suffixReaches table source target = true ↔ Ancestor graph target source := by
  constructor
  · intro accepted; exact (suffixReaches_ancestor valid.toCacheInvariant found accepted).1
  · intro ancestor
    obtain ⟨steps, path⟩ := flagged_ancestor_path valid found declared marked ancestor
    exact suffixReaches_complete valid.suffixes path

/-- Canonical cached parent tails inherit the original graph's suffix order. -/
theorem metadata_tail_preserves (valid : MetadataInvariant graph table)
    (found : lookup table parent = some entry) (ancestor : Ancestor graph parent root)
    (trace : GraphTrace graph root output tail) :
    (selectedTail table entry.mostSpecificSuffix).IsSuffix tail := by
  obtain ⟨parentOutput, parentTail, derivation, kept⟩ := trace.ancestor_tail ancestor
  have same := derivation.unique (valid.tail parent entry found)
  simpa [same.2] using kept

/-- Literal suffix containment between cached declared suffix nodes now
implies pointer reachability, rather than being assumed equivalent to it. -/
theorem literal_suffix_path (valid : MetadataInvariant graph table)
    (first : lookup table source = some left) (second : lookup table target = some right)
    (declared : graph.findNode? target = some node) (marked : node.suffix = true)
    (suffix : right.precedence.IsSuffix left.precedence) :
    ∃ steps, SuffixPath table source target steps := by
  obtain ⟨tail, trace⟩ := valid.derived source left first
  have member : target ∈ left.precedence := suffix.sublist.subset
    ((valid.tail target right second).root_mem)
  exact flagged_ancestor_path valid first declared marked (trace.covers.mp member)

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

/-- Original graph ancestry and canonical cache metadata imply pairwise
comparability of supplied parent suffix pointers; it is not an extra premise. -/
theorem parent_metadata_comparable {entries : List Linearization} (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph root output tail)
    (provenance : ∀ entry ∈ entries, ∃ name, lookup table name = some entry ∧ Ancestor graph name root) :
    ∀ left ∈ none :: entries.map (·.mostSpecificSuffix),
      ∀ right ∈ none :: entries.map (·.mostSpecificSuffix),
        SuffixDominates table left right ∨ SuffixDominates table right left := by
  intro left leftMember right rightMember
  cases left with
  | none => exact .inr trivial
  | some left =>
    cases right with
    | none => exact .inl trivial
    | some right =>
      have firstMember : some left ∈ entries.map (·.mostSpecificSuffix) := by simpa using leftMember
      have secondMember : some right ∈ entries.map (·.mostSpecificSuffix) := by simpa using rightMember
      obtain ⟨first, firstPresent, firstName⟩ := List.mem_map.mp firstMember
      obtain ⟨second, secondPresent, secondName⟩ := List.mem_map.mp secondMember
      obtain ⟨firstParent, firstFound, firstAncestor⟩ := provenance first firstPresent
      obtain ⟨secondParent, secondFound, secondAncestor⟩ := provenance second secondPresent
      obtain ⟨firstChild, firstNode, firstCached, firstDeclared, firstMarked⟩ :=
        selected_suffix_declared valid firstFound firstName
      obtain ⟨secondChild, secondNode, secondCached, secondDeclared, secondMarked⟩ :=
        selected_suffix_declared valid secondFound secondName
      have firstSuffix : firstChild.precedence.IsSuffix tail := by
        simpa [selectedTail, firstName, firstCached] using
          metadata_tail_preserves valid firstFound firstAncestor trace
      have secondSuffix : secondChild.precedence.IsSuffix tail := by
        simpa [selectedTail, secondName, secondCached] using
          metadata_tail_preserves valid secondFound secondAncestor trace
      rcases List.suffix_or_suffix_of_suffix firstSuffix secondSuffix with forward | backward
      · obtain ⟨steps, path⟩ := literal_suffix_path valid secondCached firstCached firstDeclared firstMarked forward
        exact .inr ⟨right, rfl, steps, path⟩
      · obtain ⟨steps, path⟩ := literal_suffix_path valid firstCached secondCached secondDeclared secondMarked backward
        exact .inl ⟨left, rfl, steps, path⟩

/-- Actual collected parent metadata selects successfully under graph-backed
cache metadata, without separately assuming pairwise pointer comparability. -/
theorem collected_suffix_selection_complete (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail)
    (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) :
    ∃ chosen, selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen := by
  apply selectSuffix_complete valid.suffixes
  apply parent_metadata_comparable valid trace
  intro entry member
  obtain ⟨name, present, parentTail, cached, _, _⟩ :=
    collected_parent_preserves valid.toCacheInvariant trace found collected member
  exact ⟨name, cached, .parent found present .self⟩

/-- Every successful collected selection has a real chosen cache entry and
therefore independent literal-tail certification. -/
theorem collected_suffix_selection_certified (valid : MetadataInvariant graph table)
    (collected : collectParents table names = .ok entries)
    (success : selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen) :
    ∃ certificate : TailCertified (suffixTails table (entries.map (·.mostSpecificSuffix))),
      certificate.output = selectedTail table chosen := by
  apply selectSuffix_tailCertified valid.suffixes success
  intro suffix selected
  subst chosen
  have present : some suffix ∈ entries.map (·.mostSpecificSuffix) := by
    rcases (selectSuffix_sound success).1 with impossible | member
    · cases impossible
    · exact member
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  have aligned := collectParents_sound collected
  have cachedMember : ∀ entry ∈ entries, ∃ name, lookup table name = some entry := by
    clear collected success present same member entry
    induction aligned with
    | nil => simp
    | cons cached rest ih =>
      intro entry present
      rcases List.mem_cons.mp present with same | member
      · subst entry; exact ⟨_, cached⟩
      · exact ih entry member
  obtain ⟨name, cached⟩ := cachedMember entry member
  obtain ⟨child, _, cached, _, _⟩ := selected_suffix_declared valid cached same
  exact ⟨child, cached⟩

end LeanPoo.C4.LinearizeState
