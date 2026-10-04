import LeanPoo.C4.ParentInvariant

namespace LeanPoo.C4

/-- Equal universal checks and first matching inputs. This captures stable
repeated-input deletion and is preserved by arbitrary maps. -/
structure ScanEquivalent (left right : List α) : Prop where
  all : ∀ predicate : α → Bool, left.all predicate = right.all predicate
  find : ∀ predicate : α → Bool, left.find? predicate = right.find? predicate

variable {α β : Type} {left middle right before : List α} {item : α}

theorem ScanEquivalent.refl (items : List α) : ScanEquivalent items items := ⟨fun _ => rfl, fun _ => rfl⟩

theorem ScanEquivalent.trans (first : ScanEquivalent left middle)
    (second : ScanEquivalent middle right) : ScanEquivalent left right :=
  ⟨fun p => (first.all p).trans (second.all p), fun p => (first.find p).trans (second.find p)⟩

theorem ScanEquivalent.map (same : ScanEquivalent left right) (f : α → β) :
    ScanEquivalent (left.map f) (right.map f) := by
  constructor
  · intro p; simpa only [List.all_map] using same.all (p ∘ f)
  · intro p; simp only [List.find?_map, same.find (p ∘ f)]

theorem ScanEquivalent.append (same : ScanEquivalent left right) (rest : List α) :
    ScanEquivalent (left ++ rest) (right ++ rest) := by
  constructor
  · intro p; simp only [List.all_append, same.all p]
  · intro p; simp only [List.find?_append, same.find p]

/-- A later copy cannot change an all-check or the first matching input. -/
theorem ScanEquivalent.duplicate (member : item ∈ before) (after : List α) :
    ScanEquivalent (before ++ item :: after) (before ++ after) := by
  constructor
  · intro p
    cases checked : before.all p with
    | false => simp [List.all_append, checked]
    | true =>
      have accepted := List.all_eq_true.mp checked item member
      simp [List.all_append, checked, accepted]
  · intro p
    cases found : before.find? p with
    | some entry => simp [List.find?_append, found]
    | none =>
      have rejected := List.find?_eq_none.mp found item member
      simp [List.find?_append, found, rejected]

private theorem scan_firstOccurrences (earlier names : List String) (seen : Std.HashSet String)
    (aligned : ∀ name, seen.contains name = true ↔ name ∈ earlier) :
    ScanEquivalent (earlier ++ names) (earlier ++ firstOccurrences seen names) := by
  induction names generalizing earlier seen with
  | nil => exact .refl _
  | cons name rest ih =>
    by_cases present : seen.contains name = true
    · have previous := aligned name |>.mp present
      have next := (ScanEquivalent.duplicate previous rest).trans (ih earlier seen aligned)
      simpa [firstOccurrences, present] using next
    · have newAligned : ∀ item, (seen.insert name).contains item = true ↔
          item ∈ earlier ++ [name] := by
        intro item
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, aligned,
          List.mem_append, List.mem_singleton]
        exact or_comm.trans (or_congr Iff.rfl eq_comm)
      have next := ih (earlier ++ [name]) (seen.insert name) newAligned
      simpa [firstOccurrences, present, List.append_assoc] using next

/-- The actual stable HashSet deduplication preserves every input scan. -/
theorem unique_scan (names : List String) : ScanEquivalent names (unique names) := by
  rw [unique_firstOccurrences]
  simpa using scan_firstOccurrences [] names {} (by simp)

end LeanPoo.C4

namespace LeanPoo.C4.Precedence

/-- Stable duplicate deletion preserves exact eligibility and leftmost choice. -/
theorem choose_scan (same : ScanEquivalent left right) : choose left = choose right := by
  have eligibleSame : eligible left = eligible right := by
    funext name
    exact same.all (fun order => !(order.drop 1).contains name)
  simp only [choose, heads, List.find?_filterMap]
  rw [same.all List.isEmpty, eligibleSame,
    same.find (fun order => order.head?.any (eligible right))]

/-- Scan equivalence survives every advance, even if distinct original inputs
become identical after cleanup or after consuming several heads. -/
theorem trace_scan (same : ScanEquivalent left right) : Trace left output ↔ Trace right output := by
  induction output generalizing left right with
  | nil =>
    constructor <;> intro trace <;> cases trace with
    | done empty =>
      apply Trace.done
      first | exact (same.all List.isEmpty).symm.trans empty | exact (same.all List.isEmpty).trans empty
  | cons name rest ih =>
    constructor <;> intro trace <;> cases trace with
    | step chosen next =>
      apply Trace.step
      · first | exact (choose_scan same).symm.trans chosen | exact (choose_scan same).trans chosen
      · first | exact (ih (same.map (advanceOrder name))).mp next
              | exact (ih (same.map (advanceOrder name))).mpr next

end LeanPoo.C4.Precedence

namespace LeanPoo.C4.MergeState

/-- Complete operational trace equivalence lifts to the actual optimized
merger's successful outputs and rejection domain. -/
theorem merge_trace_congr (same : ∀ output, Precedence.Trace left output ↔ Precedence.Trace right output) :
    (C4.merge left).toOption = (C4.merge right).toOption := by
  cases first : C4.merge left with
  | ok output =>
    have second := merge_complete ((same output).mp (merge_sound first))
    simp [second, Except.toOption]
  | error error =>
    cases second : C4.merge right with
    | error other => rfl
    | ok output =>
      have impossible := merge_complete ((same output).mpr (merge_sound second))
      rw [first] at impossible
      cases impossible

theorem merge_scan (same : ScanEquivalent left right) :
    (C4.merge left).toOption = (C4.merge right).toOption :=
  merge_trace_congr (fun _ => Precedence.trace_scan same)

/-- Removing empty candidates preserves successful outputs and rejection. -/
theorem merge_pending (lists : List (List String)) :
    (C4.merge (pending lists)).toOption = (C4.merge lists).toOption :=
  merge_trace_congr (fun output => trace_pending lists output)

/-- Name deduplication before mapping cached parents or cleaning their tails
preserves exact output; the map need not be injective. -/
theorem merge_unique_parents (names : List String) (order : String → List String)
    (locals : List (List String)) :
    (C4.merge (names.map order ++ locals)).toOption =
      (C4.merge ((unique names).map order ++ locals)).toOption :=
  merge_scan (((unique_scan names).map order).append locals)

private theorem pending_map_empty (orders : List (List String))
    (f : List String → List String) (empty : f [] = []) :
    pending (orders.map f) = pending ((pending orders).map f) := by
  induction orders with
  | nil => rfl
  | cons order rest ih =>
    cases order with
    | nil => simpa [pending, empty] using ih
    | cons name tail =>
      simpa only [pending, List.map_cons, List.filter_cons, List.isEmpty_cons,
        Bool.not_false, ↓reduceIte] using congrArg (fun rest =>
        if !(f (name :: tail)).isEmpty then f (name :: tail) :: rest else rest) ih

/-- Empty local orders may be removed before cleanup, even when cleanup also
turns other nonempty orders into empty candidates. -/
theorem merge_empty_locals (parents locals : List (List String))
    (cleanup : List String → List String) (empty : cleanup [] = []) :
    (C4.merge (parents ++ locals.map cleanup)).toOption =
      (C4.merge (parents ++ (pending locals).map cleanup)).toOption := by
  have same : pending (parents ++ locals.map cleanup) =
      pending (parents ++ (pending locals).map cleanup) := by
    simp only [pending, List.filter_append]
    exact congrArg (fun rest => parents.filter (fun order => !order.isEmpty) ++ rest)
      (pending_map_empty locals cleanup empty)
  rw [← merge_pending (parents ++ locals.map cleanup), same,
    merge_pending (parents ++ (pending locals).map cleanup)]

/-- The complete runtime normalization: stable parent-name deduplication and
empty local-order removal before shared-tail cleanup preserve merge output. -/
theorem merge_normalized_candidates (names : List String) (order : String → List String)
    (locals : List (List String)) (tail : List String) :
    (C4.merge (Precedence.candidates (names.map order) locals tail)).toOption =
      (C4.merge (Precedence.candidates ((unique names).map order) (pending locals) tail)).toOption := by
  simp only [Precedence.candidates, List.map_map]
  exact (merge_unique_parents names
    (fun name => (order name).filter (fun item => !tail.contains item)) _).trans
      (merge_empty_locals _ locals (fun items => items.filter (fun item => !tail.contains item)) rfl)

/-- Normalization preserves complete operational traces in both directions. -/
theorem trace_normalized_candidates (names : List String) (order : String → List String)
    (locals : List (List String)) (tail : List String) :
    Precedence.Trace (Precedence.candidates (names.map order) locals tail) output ↔
      Precedence.Trace (Precedence.candidates ((unique names).map order) (pending locals) tail) output := by
  have equivalent := merge_normalized_candidates names order locals tail
  constructor <;> intro trace
  · have merged := merge_complete trace
    have available : (C4.merge (Precedence.candidates ((unique names).map order)
        (pending locals) tail)).toOption = some output := by
      rw [← equivalent, merged]; rfl
    cases success : C4.merge (Precedence.candidates ((unique names).map order) (pending locals) tail) with
    | error error => simp [success, Except.toOption] at available
    | ok actual =>
      have same : actual = output := by simpa [success, Except.toOption] using available
      subst actual
      exact merge_sound success
  · have merged := merge_complete trace
    have available : (C4.merge (Precedence.candidates (names.map order) locals tail)).toOption = some output := by
      rw [equivalent, merged]; rfl
    cases success : C4.merge (Precedence.candidates (names.map order) locals tail) with
    | error error => simp [success, Except.toOption] at available
    | ok actual =>
      have same : actual = output := by simpa [success, Except.toOption] using available
      subst actual
      exact merge_sound success

end LeanPoo.C4.MergeState

namespace LeanPoo.C4

/-- Transport the original complete node certificate to deduplicated parent
rows and nonempty local orders, preserving both output and selected tail. -/
theorem nodeCertificate_normalize
    (certificate : NodeCertified name (names.map order ++ locals) (names.map parentTail)) :
    ∃ normalized : NodeCertified name
      ((unique names).map order ++ MergeState.pending locals) ((unique names).map parentTail),
      normalized.output = certificate.output ∧
        normalized.selection.output = certificate.selection.output := by
  let selection : TailCertified ((unique names).map parentTail) := {
    output := certificate.selection.output
    chosen := by
      rcases certificate.selection.chosen with ⟨empty, same⟩ | member
      · have noNames : names = [] := List.map_eq_nil_iff.mp empty
        exact .inl ⟨by simp [noNames, unique], same⟩
      · obtain ⟨parent, present, same⟩ := List.mem_map.mp member
        exact .inr (List.mem_map.mpr ⟨parent, unique_mem.mpr present, same⟩)
    containsTail := by
      intro tail member
      obtain ⟨parent, present, same⟩ := List.mem_map.mp member
      exact certificate.selection.containsTail tail
        (List.mem_map.mpr ⟨parent, unique_mem.mp present, same⟩)
  }
  have before : Precedence.Trace
      (Precedence.candidates (names.map order) locals certificate.selection.output)
      certificate.ancestry.front := by
    simpa [Precedence.candidates, withoutTail, List.map_append] using certificate.ancestry.trace
  have after := (MergeState.trace_normalized_candidates names order locals
    certificate.selection.output).mp before
  let ancestry : SuffixCertified ((unique names).map order ++ MergeState.pending locals)
      selection.output := {
    front := certificate.ancestry.front
    trace := by
      simpa [selection, Precedence.candidates, withoutTail, List.map_append] using after
    compatible := by
      intro input member
      apply certificate.ancestry.compatible input
      rcases List.mem_append.mp member with parent | localOrder
      · obtain ⟨name, present, same⟩ := List.mem_map.mp parent
        exact List.mem_append_left _ (List.mem_map.mpr ⟨name, unique_mem.mp present, same⟩)
      · exact List.mem_append_right _ (List.mem_filter.mp localOrder).1
  }
  refine ⟨⟨selection, ancestry, certificate.tailUnique, certificate.fresh⟩, rfl, rfl⟩

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

/-- Total projection used only in the normalization proof. Successful
collection supplies an actual entry for every name where it is used. -/
def cachedOrder (table : Table) (name : String) : List String :=
  ((lookup table name).map (·.precedence)).getD []

theorem collected_precedence_map (success : collectParents table names = .ok entries) :
    entries.map (·.precedence) = names.map (cachedOrder table) := by
  have aligned := collectParents_sound success
  clear success
  induction aligned with
  | nil => rfl
  | cons found rest ih => simp [cachedOrder, found, ih]

/-- The actual collected parent results and filtered local orders in
computeNode have exactly the merge behavior of all original declared edges. -/
theorem collected_candidates_normalize
    (success : collectParents table (parents node) = .ok entries) (tail : List String) :
    (merge ((entries.map (fun entry => withoutTail entry.precedence tail)) ++
      ((MergeState.pending node.parentOrders).map (fun order => withoutTail order tail)))).toOption =
    (merge (Precedence.candidates (node.parentOrders.flatten.map (cachedOrder table))
      node.parentOrders tail)).toOption := by
  have normalized := (MergeState.merge_normalized_candidates node.parentOrders.flatten
    (cachedOrder table) node.parentOrders tail).symm
  have mapped : entries.map (·.precedence) =
      (unique node.parentOrders.flatten).map (cachedOrder table) := by
    simpa [parents] using collected_precedence_map success
  rw [← mapped] at normalized
  simpa only [Precedence.candidates, withoutTail, List.map_map, Function.comp_def] using normalized

end LeanPoo.C4.LinearizeState
