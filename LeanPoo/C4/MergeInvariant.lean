import LeanPoo.C4.ReferenceMerge
import Std.Data.HashMap.Lemmas

namespace LeanPoo.C4.MergeState

/-- Actual tail positions, including multiplicity across repeated orders. -/
def tailNames (lists : List (List String)) : List String :=
  (lists.map (fun order => order.drop 1)).flatten

def CountInvariant (lists : List (List String)) (counts : Counts) : Prop :=
  ∀ name, counts.getD name 0 = (tailNames lists).count name

theorem increment_fold (names : List String) (counts : Counts) (name : String) :
    (names.foldl increment counts).getD name 0 = counts.getD name 0 + names.count name := by
  induction names generalizing counts with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, increment, Std.HashMap.getD_insert, List.count_cons]
    by_cases same : head = name
    · subst head; simp; omega
    · simp [same]

theorem decrement_fold (names : List String) (counts : Counts) (name : String) :
    (names.foldl decrement counts).getD name 0 = counts.getD name 0 - names.count name := by
  induction names generalizing counts with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, decrement, Std.HashMap.getD_insert, List.count_cons]
    by_cases same : head = name
    · subst head; simp; omega
    · simp [same]

private theorem ancestorCounts_fold (lists : List (List String)) (counts : Counts) (name : String) :
    (lists.foldl (fun counts order => (order.drop 1).foldl increment counts) counts).getD name 0 =
      counts.getD name 0 + (tailNames lists).count name := by
  induction lists generalizing counts with
  | nil => simp [tailNames]
  | cons order rest ih =>
    rw [List.foldl_cons, ih, increment_fold]
    simp [tailNames, Nat.add_assoc]

theorem ancestorCounts_invariant (lists : List (List String)) :
    CountInvariant lists (ancestorCounts lists) := by
  intro name
  rw [ancestorCounts, ancestorCounts_fold]
  simp

theorem zero_iff_eligible (valid : CountInvariant lists counts) (name : String) :
    (counts.getD name 0 == 0) = Precedence.eligible lists name := by
  apply Bool.eq_iff_iff.mpr
  simp only [valid name, beq_iff_eq, List.count_eq_zero, Precedence.eligible, List.all_eq_true]
  simp [tailNames, List.mem_flatten, List.mem_map]

def pending (lists : List (List String)) : List (List String) :=
  lists.filter (fun order => !order.isEmpty)

theorem tailNames_pending (lists : List (List String)) :
    tailNames (pending lists) = tailNames lists := by
  induction lists with
  | nil => rfl
  | cons order rest ih =>
    cases order <;> simp [pending, tailNames] at *
    all_goals exact ih

theorem invariant_pending (valid : CountInvariant lists counts) :
    CountInvariant (pending lists) counts := by
  intro name
  rw [tailNames_pending]
  exact valid name

theorem heads_pending (lists : List (List String)) :
    Precedence.heads (pending lists) = Precedence.heads lists := by
  induction lists with
  | nil => rfl
  | cons order rest ih =>
    cases order <;> simp [pending, Precedence.heads] at *
    all_goals simpa only [List.filterMap_cons, List.head?_nil] using ih

theorem eligibleHead_eq_choose (valid : CountInvariant lists counts) :
    eligibleHead? lists counts = Precedence.choose lists := by
  unfold eligibleHead? Precedence.choose
  simp only [zero_iff_eligible valid]
  split
  · rename_i empty
    have noHeads : Precedence.heads lists = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨order, present, head⟩ := List.mem_filterMap.mp member
      have noOrder := List.isEmpty_iff.mp (List.all_eq_true.mp empty order present)
      simp [noOrder] at head
    change (Precedence.heads lists).find? _ = none
    rw [noHeads]
    rfl
  · rfl

/-- Heads exposed by removing the selected name from matching candidates. -/
def exposedHead? (name : String) (order : List String) : Option String :=
  match order with
  | [] => none
  | head :: tail => if head == name then tail.head? else none

def exposedHeads (lists : List (List String)) (name : String) : List String :=
  lists.filterMap (exposedHead? name)

private theorem consume_fold (lists : List (List String)) (name : String)
    (nonempty : ∀ order ∈ lists, order ≠ []) (reversed : List (List String)) (heads : List String) :
    lists.foldl (consume name) (reversed, heads) =
      ((Precedence.advance lists name).reverse ++ reversed,
       (exposedHeads lists name).reverse ++ heads) := by
  induction lists generalizing reversed heads with
  | nil => simp [Precedence.advance, exposedHeads]
  | cons order rest ih =>
    have nonemptyRest : ∀ order ∈ rest, order ≠ [] :=
      fun order member => nonempty order (by simp [member])
    cases order with
    | nil => exact False.elim (nonempty [] (by simp) rfl)
    | cons head tail =>
      by_cases same : head = name
      · subst head
        cases tail <;>
          simp [List.foldl_cons, consume, ih nonemptyRest, Precedence.advance,
            Precedence.advanceOrder, exposedHeads, exposedHead?,
            List.reverse_cons, List.append_assoc]
      · simp [List.foldl_cons, consume, same, ih nonemptyRest, Precedence.advance,
          Precedence.advanceOrder, exposedHeads, exposedHead?,
          List.reverse_cons, List.append_assoc]

/-- Each removed head exposes exactly one position formerly counted as a tail.
Repeated occurrences contribute separately; no distinctness premise is used. -/
theorem tail_count_advance (lists : List (List String)) (chosen name : String) :
    (tailNames lists).count name =
      (tailNames (Precedence.advance lists chosen)).count name +
      (exposedHeads lists chosen).count name := by
  induction lists with
  | nil => simp [tailNames, Precedence.advance, exposedHeads]
  | cons order rest ih =>
    cases order with
    | nil => simpa [tailNames, Precedence.advance, Precedence.advanceOrder,
        exposedHeads, exposedHead?, List.filterMap_cons] using ih
    | cons head tail =>
      by_cases same : head = chosen
      · subst head
        cases tail with
        | nil => simpa [tailNames, Precedence.advance, Precedence.advanceOrder,
            exposedHeads, exposedHead?, List.filterMap_cons] using ih
        | cons first remaining =>
          simp [tailNames, Precedence.advance, Precedence.advanceOrder, exposedHeads,
            exposedHead?, List.count_cons] at *
          split <;> omega
      · simp [tailNames, Precedence.advance, Precedence.advanceOrder, exposedHeads,
          exposedHead?, same] at *
        omega

theorem decrement_preserves (valid : CountInvariant lists counts) (chosen : String) :
    CountInvariant (Precedence.advance lists chosen)
      ((exposedHeads lists chosen).reverse.foldl decrement counts) := by
  intro name
  rw [decrement_fold, List.count_reverse, valid name, tail_count_advance lists chosen name]
  omega

theorem choose_pending (lists : List (List String)) :
    Precedence.choose (pending lists) = Precedence.choose lists := by
  have valid := ancestorCounts_invariant lists
  rw [← eligibleHead_eq_choose (invariant_pending valid), ← eligibleHead_eq_choose valid]
  exact congrArg (fun heads => heads.find? (fun name => (ancestorCounts lists).getD name 0 == 0))
    (heads_pending lists)

theorem advance_pending (lists : List (List String)) (name : String) :
    pending (Precedence.advance (pending lists) name) =
      pending (Precedence.advance lists name) := by
  induction lists with
  | nil => rfl
  | cons order rest ih =>
    cases order with
    | nil => simpa [pending, Precedence.advance, Precedence.advanceOrder] using ih
    | cons head tail =>
      by_cases same : head = name
      · subst head
        cases tail <;> simp [pending, Precedence.advance, Precedence.advanceOrder] at *
        all_goals exact ih
      · simp [pending, Precedence.advance, Precedence.advanceOrder, same] at *
        exact ih

theorem empty_pending (lists : List (List String)) :
    (pending lists).all List.isEmpty = lists.all List.isEmpty := by
  induction lists with
  | nil => rfl
  | cons order rest ih =>
    cases order <;> simp [pending] at *
    all_goals exact ih

/-- Empty-list pruning changes neither the merge policy nor its complete traces. -/
theorem trace_pending (lists : List (List String)) (output : List String) :
    Precedence.Trace (pending lists) output ↔ Precedence.Trace lists output := by
  induction output generalizing lists with
  | nil =>
    constructor <;> intro trace <;> cases trace with
    | done empty =>
      apply Precedence.Trace.done
      simpa only [empty_pending] using empty
  | cons name output ih =>
    constructor
    · intro trace
      cases trace with
      | step chosen rest =>
        apply Precedence.Trace.step (by simpa only [choose_pending] using chosen)
        apply (ih (Precedence.advance lists name)).mp
        rw [← advance_pending]
        exact (ih _).mpr rest
    · intro trace
      cases trace with
      | step chosen rest =>
        apply Precedence.Trace.step (by simpa only [choose_pending] using chosen)
        apply (ih _).mp
        rw [advance_pending]
        exact (ih _).mpr rest

theorem mergeStep_selected (valid : CountInvariant lists counts)
    (selected : Precedence.choose lists = some name) (result : List String) :
    ∃ updated, mergeStep result lists counts =
        .ok (name :: result, pending (Precedence.advance lists name), updated) ∧
      CountInvariant (pending (Precedence.advance lists name)) updated := by
  have chosen : eligibleHead? (pending lists) counts = some name := by
    rw [eligibleHead_eq_choose (invariant_pending valid), choose_pending]
    exact selected
  have nonempty : (pending lists).isEmpty = false := by
    cases same : pending lists with
    | nil => simp [eligibleHead?, same] at chosen
    | cons _ _ => rfl
  have allNonempty : ∀ order ∈ pending lists, order ≠ [] := by
    intro order member
    have kept := (List.mem_filter.mp member).2
    simpa using kept
  have scan := consume_fold (pending lists) name allNonempty [] []
  simp only [pending] at chosen scan
  refine ⟨(exposedHeads (pending lists) name).reverse.foldl decrement counts, ?_, ?_⟩
  · simp only [mergeStep]
    change (if (pending lists).isEmpty then _ else _) = _
    simp only [nonempty, Bool.false_eq_true, ↓reduceIte, chosen, scan,
      List.append_nil, List.reverse_reverse]
    change Except.ok (name :: result, pending (Precedence.advance (pending lists) name), _) = _
    rw [advance_pending]
    rfl
  · rw [← advance_pending]
    exact invariant_pending (decrement_preserves (invariant_pending valid) name)

theorem pending_eq_nil (empty : lists.all List.isEmpty = true) : pending lists = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro order member
  simpa using List.all_eq_true.mp empty order member

theorem mergeStep_empty (empty : lists.all List.isEmpty = true) (result : List String) :
    mergeStep result lists counts = .ok (result, [], counts) := by
  simp only [mergeStep]
  have none := pending_eq_nil empty
  simp only [pending] at none
  simp [none, pure, Except.pure]

private theorem rounds_empty (empty : lists.all List.isEmpty = true)
    (valid : CountInvariant lists counts) (rounds : List Nat) (result : List String) :
    ∃ remaining, rounds.foldl round (.ok (result, lists, counts)) = .ok (result, remaining, counts) ∧
      remaining.all List.isEmpty = true ∧ CountInvariant remaining counts := by
  induction rounds generalizing lists with
  | nil => exact ⟨lists, rfl, empty, valid⟩
  | cons tick rest ih =>
    have noCount : CountInvariant [] counts := by
      have kept := invariant_pending valid
      simpa only [pending_eq_nil empty] using kept
    simpa only [List.foldl_cons, round, bind, Except.bind, mergeStep_empty empty result] using
      ih (lists := []) (by simp) noCount

/-- The actual finite fold consumes every complete trace with enough rounds,
preserving exact tail counts and the reversed emitted prefix. -/
theorem rounds_complete {rounds : List Nat} (trace : Precedence.Trace lists output)
    (valid : CountInvariant lists counts) (enough : output.length ≤ rounds.length)
    (result : List String) :
    ∃ remaining updated,
      rounds.foldl round (.ok (result, lists, counts)) = .ok (output.reverse ++ result, remaining, updated) ∧
      remaining.all List.isEmpty = true ∧ CountInvariant remaining updated := by
  induction rounds generalizing lists output result counts with
  | nil =>
    cases trace with
    | done empty => exact ⟨lists, counts, rfl, empty, valid⟩
    | step _ _ => simp at enough
  | cons tick rounds ih =>
    cases trace with
    | done empty =>
      obtain ⟨remaining, success, finished, invariant⟩ :=
        rounds_empty empty valid (tick :: rounds) result
      exact ⟨remaining, counts, success, finished, invariant⟩
    | @step lists name output selected rest =>
      obtain ⟨updated, stepSuccess, invariant⟩ := mergeStep_selected valid selected result
      have pruned := (trace_pending _ _).mpr rest
      have bound : output.length ≤ rounds.length := Nat.le_of_succ_le_succ enough
      obtain ⟨remaining, finalCounts, success, finished, finalInvariant⟩ :=
        ih pruned invariant bound (name :: result)
      refine ⟨remaining, finalCounts, ?_, finished, finalInvariant⟩
      simp only [List.foldl_cons, round, bind, Except.bind, stepSuccess]
      simpa [List.reverse_cons, List.append_assoc] using success

theorem merge_complete (trace : Precedence.Trace lists output) : C4.merge lists = .ok output := by
  have steps : lists.foldl (fun count order => count + order.length) 0 = lists.flatten.length := by
    have general (lists : List (List String)) (count : Nat) :
        lists.foldl (fun count order => count + order.length) count = count + lists.flatten.length := by
      induction lists generalizing count with
      | nil => simp
      | cons order rest ih => simp [List.foldl_cons, ih, Nat.add_assoc]
    simpa using general lists 0
  obtain ⟨remaining, counts, success, finished, _⟩ := rounds_complete (rounds := List.range lists.flatten.length) trace
    (ancestorCounts_invariant lists) (by simpa using trace.length_bound) []
  simp only [List.append_nil] at success
  simp only [C4.merge, steps, success, bind, Except.bind,
    finished, ↓reduceIte, List.reverse_reverse, pure, Except.pure]

private theorem rounds_error (rounds : List Nat) (error : Error) :
    rounds.foldl round (.error error) = .error error := by
  induction rounds with
  | nil => rfl
  | cons _ _ ih => simpa only [List.foldl_cons, round, bind, Except.bind] using ih

theorem mergeStep_blocked (valid : CountInvariant lists counts)
    (empty : lists.all List.isEmpty ≠ true) (blocked : Precedence.choose lists = none)
    (result : List String) : mergeStep result lists counts = .error .inconsistentOrder := by
  have chosen : eligibleHead? (pending lists) counts = none := by
    rw [eligibleHead_eq_choose (invariant_pending valid), choose_pending, blocked]
  have nonempty : (pending lists).isEmpty = false := by
    cases same : pending lists with
    | nil =>
      have allEmpty : (pending lists).all List.isEmpty = true := by simp [same]
      exact False.elim (empty (by simpa only [empty_pending] using allEmpty))
    | cons _ _ => rfl
  simp only [pending] at chosen
  simp only [mergeStep]
  change (if (pending lists).isEmpty then _ else _) = _
  simp [nonempty, chosen, throw]
  rfl

private theorem trace_nil_output (trace : Precedence.Trace [] output) : output = [] := by
  cases trace with
  | done _ => rfl
  | step chosen _ => simp [Precedence.choose] at chosen

/-- Every successful fold admits a trace continuation from its exact original
candidates; emitted names are bound to the actual reversed accumulator. -/
theorem rounds_sound (valid : CountInvariant lists counts) (rounds : List Nat)
    (success : rounds.foldl round (.ok (result, lists, counts)) =
      .ok (finalResult, remaining, finalCounts))
    (continuation : Precedence.Trace remaining tail) :
    ∃ emitted, Precedence.Trace lists (emitted ++ tail) ∧
      finalResult = emitted.reverse ++ result := by
  induction rounds generalizing lists counts result finalResult remaining finalCounts with
  | nil =>
    simp only [List.foldl_nil] at success
    cases Except.ok.inj success
    exact ⟨[], continuation, rfl⟩
  | cons tick rounds ih =>
    by_cases empty : lists.all List.isEmpty = true
    · have noCount : CountInvariant [] counts := by
        have kept := invariant_pending valid
        simpa only [pending_eq_nil empty] using kept
      have next : rounds.foldl round (.ok (result, [], counts)) =
          .ok (finalResult, remaining, finalCounts) := by
        simpa only [List.foldl_cons, round, bind, Except.bind, mergeStep_empty empty result] using success
      obtain ⟨emitted, trace, same⟩ := ih noCount next continuation
      have nilOutput := trace_nil_output trace
      exact ⟨emitted, by rw [nilOutput]; exact .done empty, same⟩
    · cases selected : Precedence.choose lists with
      | none =>
        have failed := mergeStep_blocked valid empty selected result
        simp only [List.foldl_cons, round, bind, Except.bind, failed, rounds_error] at success
        cases success
      | some name =>
        obtain ⟨updated, stepSuccess, invariant⟩ := mergeStep_selected valid selected result
        have next : rounds.foldl round
            (.ok (name :: result, pending (Precedence.advance lists name), updated)) =
            .ok (finalResult, remaining, finalCounts) := by
          simpa only [List.foldl_cons, round, bind, Except.bind, stepSuccess] using success
        obtain ⟨emitted, rest, same⟩ := ih invariant next continuation
        refine ⟨name :: emitted, ?_, ?_⟩
        · exact .step selected ((trace_pending _ _).mp rest)
        · simpa [List.reverse_cons, List.append_assoc] using same

theorem merge_sound (success : C4.merge lists = .ok output) : Precedence.Trace lists output := by
  let rounds := List.range (lists.foldl (fun count order => count + order.length) 0)
  let outcome := rounds.foldl round (.ok ([], lists, ancestorCounts lists))
  change (do
    let (result, remaining, _) ← outcome
    if remaining.all List.isEmpty then pure result.reverse else throw Error.inconsistentOrder) = .ok output at success
  cases observed : outcome with
  | error error => simp [observed, bind, Except.bind] at success
  | ok state =>
    obtain ⟨result, remaining, counts⟩ := state
    have empty : remaining.all List.isEmpty = true := by
      by_cases empty : remaining.all List.isEmpty = true
      · exact empty
      · simp [observed, bind, Except.bind, empty, throw] at success
    have same : result.reverse = output := by
      simpa [observed, bind, Except.bind, empty, pure, Except.pure] using success
    obtain ⟨emitted, trace, emittedEq⟩ := rounds_sound (ancestorCounts_invariant lists)
      rounds observed (.done empty)
    have outputEq : emitted = output := by simpa [emittedEq] using same
    simpa [outputEq] using trace

theorem merge_success_iff : (C4.merge lists).toOption.isSome = true ↔
    ∃ output, Precedence.Trace lists output := by
  constructor
  · intro success
    cases result : C4.merge lists with
    | error error => simp [result, Except.toOption] at success
    | ok output => exact ⟨output, merge_sound result⟩
  · rintro ⟨output, trace⟩
    simp [merge_complete trace, Except.toOption]

/-- Optimized and structural reference merging have identical successful
outputs and identical rejection domains over arbitrary finite candidates. -/
theorem merge_reference_output :
    (C4.merge lists).toOption = (Precedence.mergeReference lists).toOption.map (·.output) := by
  cases optimized : C4.merge lists with
  | error error =>
    cases reference : Precedence.mergeReference lists with
    | error other => rfl
    | ok certificate =>
      have success := merge_complete certificate.trace
      rw [optimized] at success
      cases success
  | ok output =>
    obtain ⟨certificate, success, same⟩ := Precedence.mergeReference_complete (merge_sound optimized)
    simp [Except.toOption, success, same]

end LeanPoo.C4.MergeState

namespace LeanPoo.C4.Precedence

theorem check_complete (trace : Trace lists output) : check lists output = some ⟨trace⟩ := by
  induction trace with
  | done empty => simp [check, empty]
  | step chosen rest ih =>
    simp only [check, dite_eq_left chosen, ih, Option.map_some]

/-- The existing optimized certified path reproduces every complete trace;
its independent replay cannot reject a successful optimized result. -/
theorem mergeCertified_complete (trace : Trace lists output) :
    ∃ certificate, mergeCertified lists = .ok certificate ∧ certificate.output = output := by
  refine ⟨⟨output, trace⟩, ?_, rfl⟩
  simp [mergeCertified, MergeState.merge_complete trace, check_complete trace,
    bind, Except.bind, pure, Except.pure]

theorem mergeCertified_success_iff : (mergeCertified lists).toOption.isSome = true ↔
    ∃ output, Trace lists output := by
  constructor
  · intro success
    cases result : mergeCertified lists with
    | error error => simp [result, Except.toOption] at success
    | ok certificate => exact ⟨certificate.output, certificate.trace⟩
  · rintro ⟨output, trace⟩
    obtain ⟨certificate, success, _⟩ := mergeCertified_complete trace
    simp [success, Except.toOption]

end LeanPoo.C4.Precedence
