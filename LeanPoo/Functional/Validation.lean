import LeanPoo.Functional.Assembly

/-! Ordered, all-or-error validation of finite batches at one exact context. -/
namespace LeanPoo.Functional
universe u v w x

namespace Validation
variable {Input : Type u} {Output : Type v} {Error : Type w}

/-- Stop at the first error. Later callbacks are not applied and no partial
successful batch is published. Empty batches succeed. -/
def traverse (check : Input → Except Error Output) : List Input → Except Error (List Output)
  | [] => .ok []
  | item :: rest => (check item).bind fun value =>
    (traverse check rest).map (value :: ·)

theorem traverse_append (check : Input → Except Error Output) (left right : List Input) :
    traverse check (left ++ right) =
      (traverse check left).bind (fun first => (traverse check right).map (first ++ ·)) := by
  induction left with
  | nil => simp only [List.nil_append, traverse, Except.bind]; cases traverse check right <;> rfl
  | cons item rest ih =>
    simp only [List.cons_append, traverse, ih]
    cases check item <;> cases traverse check rest <;> cases traverse check right <;> rfl

theorem traverse_success (check : Input → Except Error Output) (values : Input → Output)
    (items : List Input) (valid : ∀ item ∈ items, check item = .ok (values item)) :
    traverse check items = .ok (items.map values) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp [Except.bind, Except.map, traverse, valid item (by simp), ih (fun x hx => valid x (by simp [hx]))]

/-- Every reported error is the first failing element after a wholly successful
prefix. The suffix is arbitrary, including callbacks that would themselves fail. -/
theorem traverse_error_iff (check : Input → Except Error Output) (items : List Input) (error : Error) :
    traverse check items = .error error ↔
      ∃ before item after values, items = before ++ item :: after ∧
        traverse check before = .ok values ∧ check item = .error error := by
  constructor
  · induction items with
    | nil => simp [traverse]
    | cons item rest ih =>
      intro failed
      cases first : check item with
      | error e =>
        have same : e = error := by simpa [traverse, Except.bind, first] using failed
        subst e
        exact ⟨[], item, rest, [], rfl, rfl, first⟩
      | ok value =>
        have tail : traverse check rest = .error error := by
          cases next : traverse check rest <;> simp_all [traverse, Except.bind, Except.map]
        obtain ⟨before, bad, after, values, split, good, failure⟩ := ih tail
        exact ⟨item :: before, bad, after, value :: values,
          by simp [split], by simp [traverse, Except.bind, Except.map, first, good], failure⟩
  · rintro ⟨before, item, after, values, rfl, good, failed⟩
    rw [traverse_append, good]
    simp [traverse, Except.bind, Except.map, failed]
end Validation

namespace Factory
variable {Context : Type u} {Input : Type v} {Result : Context → Type w} {Error : Context → Type x}

/-- Validate each input at the supplied context, retaining dependent results. -/
def traverseExcept (items : List Input) (check : ∀ c, Input → Except (Error c) (Result c)) :
    Factory Context (fun c => Except (Error c) (List (Result c))) :=
  fun c => Validation.traverse (check c) items

/-- Unlike ordinary sequence, an error prevents applying the remaining factories. -/
def sequenceExcept (factories : List (Factory Context (fun c => Except (Error c) (Result c)))) :
    Factory Context (fun c => Except (Error c) (List (Result c))) :=
  fun c => Validation.traverse (fun factory => factory c) factories

theorem sequenceExcept_append
    (left right : List (Factory Context (fun c => Except (Error c) (Result c)))) (context : Context) :
    sequenceExcept (left ++ right) context =
      (sequenceExcept left context).bind (fun first => (sequenceExcept right context).map (first ++ ·)) := Validation.traverse_append _ left right
end Factory
namespace Validation
variable {Input : Type u} {Checked : Type v} {Result : Type w} {Error : Type x}

/-- The host contract's local refusal has a separate type from user exceptions. -/
def hostGuard (accepted : Bool) (value : Input) : Except Unit Input :=
  if accepted then .ok value else .error ()

/-- Translate only the local guard refusal, preserving the accepted value. -/
def refuseGuard (refusal : Error) (localResult : Except Unit Input) : Except Error Input :=
  match localResult with
  | .ok value => .ok value
  | .error () => .error refusal

/-- Observe the user predicate before entering the local guard translation. -/
def checkArgument (predicate : Input → Except Error Bool) (refusal : Error) (value : Input) :
    Except Error Input :=
  (predicate value).bind fun accepted => refuseGuard refusal (hostGuard accepted value)

/-- The previous directArgumentCheck predicate boundary, independent of the host guard. -/
def directArgumentCheck (predicate : Input → Except Error Bool) (refusal : Error) (value : Input) :
    Except Error Input :=
  match predicate value with
  | .error error => .error error
  | .ok accepted => if accepted then .ok value else .error refusal

/-- The core guard preserves every result and error, for arbitrary predicates and values. -/
theorem checkArgument_eq_direct (predicate : Input → Except Error Bool) (refusal : Error) (value) :
    checkArgument predicate refusal value = directArgumentCheck predicate refusal value := by
  cases observed : predicate value with
  | error error => simp [checkArgument, directArgumentCheck, observed, Except.bind]
  | ok accepted => cases accepted <;> simp [checkArgument, directArgumentCheck, hostGuard, refuseGuard, observed, Except.bind]

/-- A predicate error is unchanged even when it has the same family as a host error. -/
theorem predicate_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (value) (failed : predicate value = .error error) :
    checkArgument predicate refusal value = .error error := by
  simp [checkArgument, failed, Except.bind]

/-- Shape checks finish before recursive wrapping; consumers receive the wrapped value. -/
def checkThen (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value : Input) : Except Error Result :=
  (checkArgument predicate refusal value).bind fun original => (normalize original).bind consume

/-- The entire workflow preserves the previous direct predicate boundary, including body errors. -/
theorem checkThen_eq_direct (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result) (value) :
    checkThen predicate refusal normalize consume value =
      (directArgumentCheck predicate refusal value).bind (fun original => (normalize original).bind consume) := by
  simp only [checkThen, checkArgument_eq_direct]

/-- A failed shape check stops before normalization and observation. -/
theorem rejected (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value) (failed : predicate value = .ok false) :
    checkThen predicate refusal normalize consume value = .error refusal := by
  simp [checkThen, checkArgument, failed, hostGuard, refuseGuard, Except.bind]

/-- Successful wrapping feeds the checked result, rather than the original, to the consumer. -/
theorem normalized (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value checked) (accepted : predicate value = .ok true)
    (wrapped : normalize value = .ok checked) :
    checkThen predicate refusal normalize consume value = consume checked := by
  simp [checkThen, checkArgument, accepted, wrapped, hostGuard, refuseGuard, Except.bind]

/-- Normalizer errors, including recursive budget/cycle refusals, are never remapped. -/
theorem normalization_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value) (accepted : predicate value = .ok true) (failed : normalize value = .error error) :
    checkThen predicate refusal normalize consume value = .error error := by
  simp [checkThen, checkArgument, accepted, failed, hostGuard, refuseGuard, Except.bind]

/-- An error from a checked consumer is not caught by the local host guard. -/
theorem consumer_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value checked) (accepted : predicate value = .ok true)
    (wrapped : normalize value = .ok checked) (failed : consume checked = .error error) :
    checkThen predicate refusal normalize consume value = .error error := by
  rw [normalized predicate refusal normalize consume value checked accepted wrapped, failed]

/-- Ordered batches inherit the same equivalence without a second traversal implementation. -/
theorem batchArgument_eq_direct (predicate : Input → Except Error Bool) (refusal : Error)
    (values : List Input) :
    Validation.traverse (checkArgument predicate refusal) values =
      Validation.traverse (directArgumentCheck predicate refusal) values := by
  have same : checkArgument predicate refusal = directArgumentCheck predicate refusal :=
    funext (checkArgument_eq_direct predicate refusal)
  rw [same]
end Validation

namespace Validation
/-- Ordered diagnostic collection models the standard builder's append-one law.
The callback returns a finite proper issue list for each child. -/
def gatherIssues (check : Input → List Issue) (values : List Input) (initial : List Issue := []) : List Issue :=
  values.foldl (fun collected value => collected ++ check value) initial

/-- Replacing a list of intermediate lists with one builder preserves all issue
positions, multiplicity and child order, including empty child diagnostics. -/
theorem gatherIssues_eq_flatMap (check : Input → List Issue) (values : List Input) (initial : List Issue) :
    gatherIssues check values initial = initial ++ values.flatMap check := by
  induction values generalizing initial with
  | nil => simp [gatherIssues]
  | cons value rest ih =>
    simpa only [gatherIssues, List.foldl_cons, List.flatMap_cons, List.append_assoc] using
      ih (initial ++ check value)

end Validation

end LeanPoo.Functional
