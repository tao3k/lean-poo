import LeanPoo.C4.GraphCertificate
import Std.Data.HashMap.Lemmas

namespace LeanPoo.C4.LinearizeState

private theorem indexStep_lookup (table : Std.HashMap String Node) (node : Node) (name : String) :
    (indexStep table node)[name]? =
      (table[name]?).orElse (fun _ => if node.name == name then some node else none) := by
  unfold indexStep
  split
  · rename_i present
    by_cases same : node.name = name
    · rw [same] at present
      have available : (table[name]?).isSome = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at present
        exact present
      cases found : table[name]? with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at available
      | some entry => simp [Option.orElse]
    · cases table[name]? <;> simp [same, Option.orElse]
  · rename_i absent
    rw [Std.HashMap.getElem?_insert]
    by_cases same : node.name = name
    · rw [same] at absent
      have missing : table[name]? = none := Std.HashMap.getElem?_eq_none_of_contains_eq_false (Bool.eq_false_iff.mpr absent)
      simp [same, missing, Option.orElse]
    · simp [same, Option.orElse]
      cases table[name]? <;> rfl

private theorem index_fold (nodes : List Node) (table : Std.HashMap String Node) (name : String) :
    (nodes.foldl indexStep table)[name]? =
      (table[name]?).orElse (fun _ => nodes.find? (fun node => node.name == name)) := by
  induction nodes generalizing table with
  | nil => simp only [List.foldl_nil, List.find?_nil]; cases table[name]? <;> simp [Option.orElse]
  | cons node rest ih =>
    rw [List.foldl_cons, ih, indexStep_lookup]
    cases table[name]? <;> by_cases same : node.name = name <;>
      simp [same, Option.orElse]

/-- The actual first-write hash index agrees with the original graph lookup,
including duplicate declarations and absent names. -/
theorem nodeIndex_lookup (graph : Graph) (name : String) :
    (nodeIndex graph)[name]? = graph.findNode? name := by
  rw [nodeIndex, index_fold]
  simp [Graph.findNode?, Option.orElse]

theorem nodeIndex_declared (found : (nodeIndex graph)[name]? = some node) :
    node ∈ graph.nodes ∧ node.name = name := by
  rw [nodeIndex_lookup] at found
  exact ⟨List.mem_of_find?_eq_some found, beq_iff_eq.mp (List.find?_some (p := fun declaration : Node => declaration.name == name) found)⟩

/-- Finite pointer paths follow exact cached inherited-suffix lookups.
The index counts links; recognition at the target needs one further round. -/
inductive SuffixPath (table : Table) : String → String → Nat → Prop where
  | here : SuffixPath table name name 0
  | next (found : lookup table source = some entry)
      (link : entry.inheritedSuffix = some next)
      (rest : SuffixPath table next target steps) : SuffixPath table source target (steps + 1)

theorem SuffixPath.trans (first : SuffixPath table source middle firstSteps)
    (second : SuffixPath table middle target secondSteps) :
    SuffixPath table source target (secondSteps + firstSteps) := by
  induction first with
  | here => exact second
  | next found link rest ih =>
    simpa [Nat.add_assoc] using SuffixPath.next found link (ih second)

private def WalkValid (table : Table) (source target : String) (state : Option String × Bool) : Prop :=
  (state.2 = true → ∃ steps, SuffixPath table source target steps) ∧
    ∀ name, state.1 = some name → ∃ steps, SuffixPath table source name steps

private theorem suffixStep_sound (valid : WalkValid table source target state) (tick : Nat) :
    WalkValid table source target (suffixStep table target state tick) := by
  obtain ⟨current, found⟩ := state
  rcases valid with ⟨finished, reached⟩
  cases found with
  | true => simpa only [suffixStep, WalkValid, Bool.true_eq, ↓reduceIte] using And.intro finished reached
  | false =>
    cases current with
    | none => simp [suffixStep, WalkValid]
    | some name =>
      obtain ⟨steps, path⟩ := reached name rfl
      by_cases same : name = target
      · subst target
        simpa [suffixStep, WalkValid] using
          (show ∃ steps, SuffixPath table source name steps from ⟨steps, path⟩)
      · simp only [suffixStep, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, ite_eq_right same]
        refine ⟨by simp, ?_⟩
        intro next pointer
        cases cached : lookup table name with
        | none => simp [cached] at pointer
        | some entry =>
          have link : entry.inheritedSuffix = some next := by simpa [cached] using pointer
          exact ⟨1 + steps, path.trans (.next cached link .here)⟩

private theorem suffixRounds_sound (rounds : List Nat) (valid : WalkValid table source target state) :
    WalkValid table source target (rounds.foldl (suffixStep table target) state) := by
  induction rounds generalizing state with
  | nil => exact valid
  | cons tick rest ih => exact ih (suffixStep_sound valid tick)

/-- Successful recognition by the actual bounded walk always has a finite
pointer derivation, without any cache-validity premise. -/
theorem suffixReachesWithFuel_sound (accepted : suffixReachesWithFuel table source target fuel = true) :
    ∃ steps, SuffixPath table source target steps := by
  have initial : WalkValid table source target (some source, false) :=
    ⟨by simp, fun name same => by cases same; exact ⟨0, .here⟩⟩
  exact (suffixRounds_sound (List.range fuel) initial).1 accepted

private theorem suffixRounds_found (rounds : List Nat) :
    (rounds.foldl (suffixStep table target) (current, true)).2 = true := by
  induction rounds with
  | nil => rfl
  | cons tick rest ih => simpa [List.foldl_cons, suffixStep] using ih

private theorem suffixRounds_complete {rounds : List Nat} (path : SuffixPath table source target steps)
    (enough : steps + 1 ≤ rounds.length) :
    (rounds.foldl (suffixStep table target) (some source, false)).2 = true := by
  induction path generalizing rounds with
  | @here name =>
    cases rounds with
    | nil => simp at enough
    | cons tick rest =>
      simpa [List.foldl_cons, suffixStep] using
        (suffixRounds_found (table := table) (target := name) (current := some name) rest)
  | @next source entry next target steps found link rest ih =>
    cases rounds with
    | nil => simp at enough
    | cons tick rounds =>
      by_cases same : source = target
      · subst target
        simpa [List.foldl_cons, suffixStep] using
          (suffixRounds_found (table := table) (target := source) (current := some source) rounds)
      · have remaining : steps + 1 ≤ rounds.length := by simpa using Nat.le_of_succ_le_succ enough
        simpa [List.foldl_cons, suffixStep, same, found, link] using ih remaining

theorem suffixReachesWithFuel_complete (path : SuffixPath table source target steps)
    (enough : steps + 1 ≤ fuel) : suffixReachesWithFuel table source target fuel = true :=
  suffixRounds_complete path (by simpa using enough)

/-- Cached suffix links retain a literal tail of the source precedence. Every
cached precedence has its own lookup name at the head. This is the invariant
required of the ordinary compiler's populated table, not an assumed theorem
about tables produced by its traversal. -/
structure SuffixCacheInvariant (table : Table) : Prop where
  head : ∀ name entry, lookup table name = some entry → entry.precedence.head? = some name
  link : ∀ source entry, lookup table source = some entry → ∀ next,
    entry.inheritedSuffix = some next → ∃ child, lookup table next = some child ∧
      child.precedence.IsSuffix entry.precedence.tail

private theorem precedence_tail (items : List String) : items.tail.IsSuffix items := by
  cases items with
  | nil => exact ⟨[], rfl⟩
  | cons head tail => exact ⟨[head], rfl⟩

private theorem link_decreases {child : Linearization} (valid : SuffixCacheInvariant table)
    (found : lookup table source = some entry)
    (kept : child.precedence.IsSuffix entry.precedence.tail) :
    child.precedence.length < entry.precedence.length := by
  have head := valid.head source entry found
  have shorter : entry.precedence.tail.length < entry.precedence.length := by
    cases actual : entry.precedence with
    | nil => simp [actual] at head
    | cons _ _ => simp
  exact Nat.lt_of_le_of_lt kept.length_le shorter

theorem SuffixPath.endpoint (path : SuffixPath table source target steps)
    (valid : SuffixCacheInvariant table) (found : lookup table source = some entry) :
    ∃ last, lookup table target = some last ∧ last.precedence.IsSuffix entry.precedence ∧
      (0 < steps → last.precedence.length < entry.precedence.length) := by
  induction path generalizing entry with
  | here => exact ⟨entry, found, List.suffix_refl _, by omega⟩
  | @next source original next target steps selected link rest ih =>
    have identical := Option.some.inj (selected.symm.trans found)
    subst original
    obtain ⟨child, childFound, kept⟩ := valid.link source entry found next link
    obtain ⟨last, lastFound, inherited, _⟩ := ih childFound
    refine ⟨last, lastFound, inherited.trans (kept.trans (precedence_tail _)), ?_⟩
    intro _
    exact Nat.lt_of_le_of_lt inherited.length_le (link_decreases valid found kept)

theorem SuffixPath.ne (path : SuffixPath table source target steps)
    (valid : SuffixCacheInvariant table) (found : lookup table source = some entry)
    (positive : 0 < steps) : source ≠ target := by
  intro same
  obtain ⟨last, lastFound, _, shorter⟩ := path.endpoint valid found
  rw [← same] at lastFound
  have identical := Option.some.inj (found.symm.trans lastFound)
  subst last
  exact Nat.lt_irrefl _ (shorter positive)

private theorem path_visited (path : SuffixPath table source target steps)
    (valid : SuffixCacheInvariant table) :
    ∃ names : List String, names.length = steps ∧ names.Nodup ∧
      ∀ name ∈ names, (lookup table name).isSome = true ∧
        ∃ hops, SuffixPath table source name hops := by
  induction path with
  | here => exact ⟨[], rfl, List.nodup_nil, by simp⟩
  | @next source entry next target steps found link rest ih =>
    obtain ⟨names, length, unique, members⟩ := ih
    have absent : source ∉ names := by
      intro member
      obtain ⟨_, hops, returning⟩ := members source member
      exact (SuffixPath.next found link returning).ne valid found (Nat.succ_pos _) rfl
    refine ⟨source :: names, by simp [length], List.nodup_cons.mpr ⟨absent, unique⟩, ?_⟩
    intro name member
    rcases List.mem_cons.mp member with same | member
    · subst name
      exact ⟨by simp [found], 0, .here⟩
    · obtain ⟨present, hops, earlier⟩ := members name member
      exact ⟨present, hops + 1, .next found link earlier⟩

/-- Strict cached suffix links cannot revisit a name. Every traversed link
source is an actual key, so the number of links is bounded by table size. -/
theorem SuffixPath.length_bound (path : SuffixPath table source target steps)
    (valid : SuffixCacheInvariant table) : steps ≤ table.size := by
  obtain ⟨names, length, unique, members⟩ := path_visited path valid
  have subset : ∀ name ∈ names, name ∈ table.keys := by
    intro name member
    apply Std.HashMap.mem_keys.mpr
    have present := (members name member).1
    change table[name]?.isSome = true at present
    exact Std.HashMap.mem_iff_isSome_getElem?.mpr present
  have bound := unique.length_le_of_subset subset
  simpa only [length, Std.HashMap.length_keys] using bound

theorem suffixReaches_sound (accepted : suffixReaches table source target = true) :
    ∃ steps, SuffixPath table source target steps := suffixReachesWithFuel_sound accepted

theorem suffixReaches_complete (valid : SuffixCacheInvariant table)
    (path : SuffixPath table source target steps) : suffixReaches table source target = true :=
  suffixReachesWithFuel_complete path (Nat.add_le_add_right (path.length_bound valid) 1)

theorem suffixReaches_iff (valid : SuffixCacheInvariant table) :
    suffixReaches table source target = true ↔ ∃ steps, SuffixPath table source target steps :=
  ⟨suffixReaches_sound, fun ⟨_, path⟩ => suffixReaches_complete valid path⟩

/-- A successful walk retains the target cached precedence as a literal
suffix of the source cached precedence. -/
theorem suffixReaches_preserves (valid : SuffixCacheInvariant table)
    (found : lookup table source = some entry) (accepted : suffixReaches table source target = true) :
    ∃ last, lookup table target = some last ∧ last.precedence.IsSuffix entry.precedence := by
  obtain ⟨steps, path⟩ := suffixReaches_sound accepted
  obtain ⟨last, selected, kept, _⟩ := path.endpoint valid found
  exact ⟨last, selected, kept⟩

/-- Cache provenance for complete precedence and inherited-suffix links.
The most-specific-suffix selector and traversal population are separate
obligations; this structure does not assert either is already verified. -/
structure CacheInvariant (graph : Graph) (table : Table) : Prop where
  suffixes : SuffixCacheInvariant table
  derived : ∀ name entry, lookup table name = some entry →
    ∃ tail, GraphTrace graph name entry.precedence tail

theorem CacheInvariant.empty (graph : Graph) : CacheInvariant graph ({} : Table) := by
  constructor
  · constructor <;> intro name entry found <;> simp [lookup] at found
  · intro name entry found
    simp [lookup] at found

theorem lookup_insert (table : Table) (name query : String) (entry : Linearization) :
    lookup (table.insert name entry) query =
      if name == query then some entry else lookup table query := by
  exact Std.HashMap.get?_insert

/-- The actual fresh cache insertion preserves provenance and literal suffix
links once the computed entry supplies its graph derivation and link evidence. -/
theorem CacheInvariant.insert (valid : CacheInvariant graph table)
    (fresh : lookup table name = none) (trace : GraphTrace graph name entry.precedence tail)
    (links : ∀ next, entry.inheritedSuffix = some next →
      ∃ child, lookup table next = some child ∧ child.precedence.IsSuffix entry.precedence.tail) :
    CacheInvariant graph (table.insert name entry) := by
  have retained {query : String} {child : Linearization} (found : lookup table query = some child) :
      lookup (table.insert name entry) query = some child := by
    have different : name ≠ query := by
      intro same
      subst query
      rw [fresh] at found
      cases found
    simp [lookup_insert, different, found]
  constructor
  · constructor
    · intro query cached found
      by_cases same : name = query
      · subst query
        have identical : entry = cached := by simpa [lookup_insert] using found
        subst cached
        exact trace.head
      · have original : lookup table query = some cached := by
          simpa [lookup_insert, same] using found
        exact valid.suffixes.head query cached original
    · intro query cached found next link
      by_cases same : name = query
      · subst query
        have identical : entry = cached := by simpa [lookup_insert] using found
        subst cached
        obtain ⟨child, selected, kept⟩ := links next link
        exact ⟨child, retained selected, kept⟩
      · have original : lookup table query = some cached := by
          simpa [lookup_insert, same] using found
        obtain ⟨child, selected, kept⟩ := valid.suffixes.link query cached original next link
        exact ⟨child, retained selected, kept⟩
  · intro query cached found
    by_cases same : name = query
    · subst query
      have identical : entry = cached := by simpa [lookup_insert] using found
      subst cached
      exact ⟨tail, trace⟩
    · exact valid.derived query cached (by simpa [lookup_insert, same] using found)

/-- Under cache provenance, the actual suffix walk witnesses original-graph
ancestry and the target's complete graph-derived precedence as a literal suffix. -/
theorem suffixReaches_ancestor (valid : CacheInvariant graph table)
    (found : lookup table source = some entry) (accepted : suffixReaches table source target = true) :
    Ancestor graph target source ∧ ∃ last tail, lookup table target = some last ∧
      GraphTrace graph target last.precedence tail ∧ last.precedence.IsSuffix entry.precedence := by
  obtain ⟨last, selected, kept⟩ := suffixReaches_preserves valid.suffixes found accepted
  obtain ⟨sourceTail, sourceTrace⟩ := valid.derived source entry found
  obtain ⟨targetTail, targetTrace⟩ := valid.derived target last selected
  exact ⟨sourceTrace.covers.mp (kept.sublist.subset targetTrace.root_mem),
    last, targetTail, selected, targetTrace, kept⟩

end LeanPoo.C4.LinearizeState
