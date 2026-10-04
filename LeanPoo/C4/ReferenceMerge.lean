import LeanPoo.C4.Precedence

namespace LeanPoo.C4.Precedence

/-- A complete trace cannot emit more names than the input candidate positions. -/
theorem Trace.length_bound (trace : Trace lists output) : output.length ≤ lists.flatten.length :=
  trace.nodup.length_le_of_subset (fun _ member => List.mem_flatten.mpr (trace.covers.mp member))

/-- Structural reference merger. Every successful step constructs its trace
directly; no optimized tail-count state or supplied output is involved. -/
def mergeReferenceWithFuel (lists : List (List String)) : Nat → Except C4.Error (Certified lists)
  | 0 =>
    if empty : lists.all List.isEmpty = true then .ok ⟨[], .done empty⟩
    else .error .inconsistentOrder
  | fuel + 1 =>
    if empty : lists.all List.isEmpty = true then .ok ⟨[], .done empty⟩
    else
      match selected : choose lists with
      | none => .error .inconsistentOrder
      | some name => do
        let rest ← mergeReferenceWithFuel (advance lists name) fuel
        return ⟨name :: rest.output, .step selected rest.trace⟩

/-- Any complete trace is reproduced when enough steps are available. -/
theorem mergeReferenceWithFuel_complete (trace : Trace lists output)
    (enough : output.length ≤ fuel) :
    ∃ result, mergeReferenceWithFuel lists fuel = .ok result ∧ result.output = output := by
  induction trace generalizing fuel with
  | done empty =>
    refine ⟨⟨[], .done empty⟩, ?_, rfl⟩
    cases fuel <;> simp [mergeReferenceWithFuel, empty]
  | @step lists name output selected rest ih =>
    have nonempty : lists.all List.isEmpty ≠ true := by
      intro empty
      simp [choose, empty] at selected
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have smaller : output.length ≤ fuel := Nat.le_of_succ_le_succ enough
      obtain ⟨result, success, same⟩ := ih smaller
      refine ⟨⟨name :: result.output, .step selected result.trace⟩, ?_, ?_⟩
      · simp only [mergeReferenceWithFuel, dite_eq_right nonempty]
        split
        · rename_i choice
          rw [choice] at selected
          cases selected
        · rename_i other choice
          have chosen : other = name := Option.some.inj (choice.symm.trans selected)
          subst other
          rw [success]
          rfl
      · simp [same]

def mergeReference (lists : List (List String)) : Except C4.Error (Certified lists) :=
  mergeReferenceWithFuel lists lists.flatten.length

/-- Completeness for arbitrary finite candidate lists, without a graph-size
assumption or a bound supplied by the caller. -/
theorem mergeReference_complete (trace : Trace lists output) :
    ∃ result, mergeReference lists = .ok result ∧ result.output = output :=
  mergeReferenceWithFuel_complete trace trace.length_bound

theorem mergeReference_success_iff :
    (mergeReference lists).toOption.isSome = true ↔ ∃ output, Trace lists output := by
  constructor
  · intro success
    cases result : mergeReference lists with
    | error error => simp [result, Except.toOption] at success
    | ok certificate => exact ⟨certificate.output, certificate.trace⟩
  · rintro ⟨output, trace⟩
    obtain ⟨result, success, _⟩ := mergeReference_complete trace
    simp [success, Except.toOption]

end LeanPoo.C4.Precedence
