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
end LeanPoo.Functional
