import LeanPoo.Prototype.C3

/-! One-step correspondence between the paper's C3 merge pseudocode and the
certifying precedence merge reused by the Lean implementation. This concerns
candidate lists; recursive graph lookup and cache validity are separate. -/

namespace LeanPoo.Prototype.C3

open LeanPoo.C4

/-- Paper `candidate?`: a name may not occur in any candidate tail. -/
def sourceEligible (lists : List (List String)) (name : String) : Bool :=
  (removeNulls lists).all fun order => !(order.drop 1).contains name

/-- Paper `c3-select-next`: scan the nonempty heads from left to right. -/
def sourceChoose (lists : List (List String)) : Option String :=
  ((removeNulls lists).filterMap List.head?).find? (sourceEligible lists)

private theorem heads_removeNulls (lists : List (List String)) :
    (removeNulls lists).filterMap List.head? = Precedence.heads lists := by
  induction lists with
  | nil => rfl
  | cons row rows ih =>
    cases row with
    | nil => simpa [removeNulls, Precedence.heads, List.filterMap_cons] using ih
    | cons head tail =>
      have ih' : (removeNulls rows).filterMap List.head? =
          rows.filterMap List.head? := by simpa [Precedence.heads] using ih
      simpa [removeNulls, Precedence.heads, List.filterMap_cons] using
        congrArg (head :: ·) ih'

theorem sourceEligible_eq (lists : List (List String)) (name : String) :
    sourceEligible lists name = Precedence.eligible lists name := by
  induction lists with
  | nil => rfl
  | cons row rows ih =>
    cases row with
    | nil => simpa [sourceEligible, removeNulls, Precedence.eligible] using ih
    | cons head tail =>
      simp [sourceEligible, removeNulls, Precedence.eligible] at ih ⊢
      rw [ih]

private theorem removeNulls_empty_of_all (lists : List (List String))
    (empty : lists.all List.isEmpty = true) : removeNulls lists = [] := by
  induction lists with
  | nil => rfl
  | cons row rows ih =>
    have rowEmpty := List.all_eq_true.mp empty row (List.mem_cons_self ..)
    have rowsEmpty : rows.all List.isEmpty = true := by
      apply List.all_eq_true.mpr
      intro value member
      exact List.all_eq_true.mp empty value (List.mem_cons_of_mem row member)
    have rowNil : row = [] := List.isEmpty_iff.mp rowEmpty
    subst row
    simpa [removeNulls] using ih rowsEmpty

/-- The paper's leftmost eligible head is exactly the certified merge choice,
even when the original list includes empty rows. -/
theorem sourceChoose_eq (lists : List (List String)) :
    sourceChoose lists = Precedence.choose lists := by
  unfold sourceChoose Precedence.choose
  by_cases empty : lists.all List.isEmpty = true
  · simp [empty, removeNulls_empty_of_all lists empty]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
    rw [heads_removeNulls]
    congr 1
    funext name
    exact sourceEligible_eq lists name

theorem removeNext_eq_advance (lists : List (List String)) (name : String) :
    removeNext name lists = removeNulls (Precedence.advance lists name) := by
  unfold removeNext Precedence.advance
  congr 1
  apply List.map_congr_left
  intro row _
  cases row with
  | nil => rfl
  | cons head tail =>
    simp [Precedence.advanceOrder]

theorem removeNulls_idempotent (lists : List (List String)) :
    removeNulls (removeNulls lists) = removeNulls lists := by
  induction lists with
  | nil => rfl
  | cons row rows ih =>
    cases row with
    | nil => simp [removeNulls]
    | cons head tail => simp [removeNulls]

theorem removeNext_normalized (lists : List (List String)) (name : String) :
    removeNext name (removeNulls lists) = removeNext name lists := by
  induction lists with
  | nil => rfl
  | cons row rows ih =>
    cases row with
    | nil => simpa [removeNulls, removeNext] using ih
    | cons head tail =>
      simp only [removeNext, removeNulls] at ih
      simp only [beq_iff_eq] at ih
      by_cases same : head = name
      · simp [removeNulls, removeNext, same]
        by_cases tailEmpty : tail.isEmpty
        · simpa [tailEmpty] using ih
        · simpa [tailEmpty] using congrArg (tail :: ·) ih
      · simp [removeNulls, removeNext, same, ih]

theorem sourceChoose_normalized (lists : List (List String)) :
    sourceChoose (removeNulls lists) = sourceChoose lists := by
  have sameEligible : sourceEligible (removeNulls lists) = sourceEligible lists := by
    funext name
    simp [sourceEligible, removeNulls_idempotent]
  simp [sourceChoose, removeNulls_idempotent, sameEligible]

/-- A paper C3 merge trace keeps only nonempty candidate rows after a step. -/
inductive SourceTrace : List (List String) → List String → Prop where
  | done (empty : removeNulls lists = []) : SourceTrace lists []
  | step (chosen : sourceChoose lists = some name)
      (rest : SourceTrace (removeNext name lists) output) :
      SourceTrace lists (name :: output)

theorem SourceTrace.normalize (trace : SourceTrace lists output) :
    SourceTrace (removeNulls lists) output := by
  cases trace with
  | done empty =>
    exact .done (by simpa [removeNulls_idempotent] using empty)
  | @step lists name output chosen rest =>
    have next : removeNext name (removeNulls lists) = removeNext name lists :=
      removeNext_normalized lists name
    exact .step (by simpa [sourceChoose_normalized] using chosen)
      (by simpa [next] using rest)

/-- Every certified optimized merge has the paper's same-step source trace. -/
theorem SourceTrace.ofCertified (trace : Precedence.Trace lists output) :
    SourceTrace lists output := by
  induction trace with
  | @done lists empty => exact .done (removeNulls_empty_of_all lists empty)
  | @step lists name output chosen rest ih =>
    have selected : sourceChoose lists = some name := by
      rw [sourceChoose_eq]
      exact chosen
    have next : removeNext name lists =
        removeNulls (Precedence.advance lists name) :=
      removeNext_eq_advance lists name
    exact .step selected (by rw [next]; exact ih.normalize)

theorem SourceTrace.unique (first : SourceTrace lists output₁)
    (second : SourceTrace lists output₂) : output₁ = output₂ := by
  induction first generalizing output₂ with
  | done empty =>
    cases second with
    | done _ => rfl
    | step chosen _ => simp [sourceChoose, empty] at chosen
  | @step lists name output chosen rest ih =>
    cases second with
    | done empty => simp [sourceChoose, empty] at chosen
    | @step _ other tail selected next =>
      have same : name = other := Option.some.inj (chosen.symm.trans selected)
      subst other
      exact congrArg (name :: ·) (ih next)

/-- A successful C3 merge carries proofs that every input list is retained
in order, every output name came from an input, and the result has no repeats. -/
def mergeCertified (lists : List (List String)) :
    Except C4.Error (Precedence.Certified lists) :=
  Precedence.mergeCertified lists

theorem mergeCertified_sourceTrace (lists : List (List String))
    (certificate : Precedence.Certified lists) :
    SourceTrace lists certificate.output :=
  SourceTrace.ofCertified certificate.trace

theorem SourceTrace.eq_certified (trace : SourceTrace lists output)
    (certificate : Precedence.Certified lists) :
    output = certificate.output :=
  trace.unique (mergeCertified_sourceTrace lists certificate)

theorem mergeCertified_preserves (lists : List (List String))
    (certificate : Precedence.Certified lists) (order : List String)
    (member : order ∈ lists) : order.Sublist certificate.output :=
  certificate.trace.preserves member

theorem mergeCertified_covers (lists : List (List String))
    (certificate : Precedence.Certified lists) (name : String) :
    name ∈ certificate.output ↔ ∃ order ∈ lists, name ∈ order :=
  certificate.trace.covers

theorem mergeCertified_nodup (lists : List (List String))
    (certificate : Precedence.Certified lists) : certificate.output.Nodup :=
  certificate.trace.nodup

end LeanPoo.Prototype.C3
