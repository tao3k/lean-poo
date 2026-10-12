import LeanPoo.Prototype.DynamicCodec

/-! Computable, kernel justified equality for dynamic call arguments. Ordered
lists, dictionary entries and duplicate raw object fields remain part of a
value; function and descriptor references compare their explicit identities. -/
namespace LeanPoo.Prototype.Dynamic

private def orderedEqual (equal : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | left :: rest, right :: tail => equal left right && orderedEqual equal rest tail
  | _, _ => false

private theorem orderedEqual_correct (left right : List α) (equal : α → α → Bool)
    (correct : ∀ item ∈ left, ∀ other, equal item other = true ↔ item = other) :
    orderedEqual equal left right = true ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [orderedEqual]
  | cons head tail ih =>
    cases right with
    | nil => simp [orderedEqual]
    | cons other rest =>
      simp only [orderedEqual, Bool.and_eq_true, List.cons.injEq]
      rw [correct head (by simp) other, ih rest (fun item member => correct item (by simp [member]))]

def Value.equalAt : Nat → Value → Value → Bool
  | 0, _, _ => false
  | fuel + 1, left, right =>
    match left, right with
    | .unit, .unit => true
    | .boolean left, .boolean right => left == right
    | .integer left, .integer right => left == right
    | .text left, .text right => left == right
    | .list left, .list right => orderedEqual (Value.equalAt fuel) left right
    | .dictionary left, .dictionary right =>
      orderedEqual (fun left right => Value.equalAt fuel left.1 right.1 &&
        Value.equalAt fuel left.2 right.2) left right
    | .object left, .object right =>
      orderedEqual (fun left right => left.1 == right.1 &&
        Value.equalAt fuel left.2 right.2) left right
    | .function left, .function right | .descriptor left, .descriptor right => left == right
    | _, _ => false

/-- The left value's structural depth suffices even when the right value is
larger. No registry lookup, hash, wire parser or unsafe equality is trusted. -/
theorem Value.equalAt_correct (left right : Value) (fuel : Nat)
    (bound : left.wireDepth ≤ fuel) : left.equalAt fuel right = true ↔ left = right := by
  induction fuel generalizing left right with
  | zero => have positive := left.wireDepth_pos; omega
  | succ fuel ih =>
    cases left with
    | unit => cases right <;> simp [Value.equalAt]
    | boolean value => cases right <;> simp [Value.equalAt]
    | integer value => cases right <;> simp [Value.equalAt]
    | text value => cases right <;> simp [Value.equalAt]
    | function identity => cases right <;> simp [Value.equalAt]
    | descriptor identity => cases right <;> simp [Value.equalAt]
    | list values =>
      cases right <;> try { simp [Value.equalAt]; done }
      rename_i others
      simp only [Value.equalAt, Value.list.injEq]
      apply orderedEqual_correct
      intro child member other
      have height := List.le_max?_getD_of_mem (k := 0)
        (List.mem_map_of_mem (f := Value.wireDepth) member)
      exact ih child other (by simp_all [Value.wireDepth]; omega)
    | dictionary entries =>
      cases right <;> try { simp [Value.equalAt]; done }
      rename_i others
      simp only [Value.equalAt, Value.dictionary.injEq]
      apply orderedEqual_correct
      intro entry member other
      have height := List.le_max?_getD_of_mem (k := 0)
        (List.mem_map_of_mem (f := fun entry : Value × Value =>
          max entry.1.wireDepth entry.2.wireDepth) member)
      have first := ih entry.1 other.1 (by simp_all [Value.wireDepth]; omega)
      have second := ih entry.2 other.2 (by simp_all [Value.wireDepth]; omega)
      simp [first, second, Prod.ext_iff]
    | object entries =>
      cases right <;> try { simp [Value.equalAt]; done }
      rename_i others
      simp only [Value.equalAt, Value.object.injEq]
      apply orderedEqual_correct
      intro entry member other
      have height := List.le_max?_getD_of_mem (k := 0)
        (List.mem_map_of_mem (f := fun entry : String × Value => entry.2.wireDepth) member)
      have second := ih entry.2 other.2 (by simp_all [Value.wireDepth]; omega)
      simp [second, Prod.ext_iff]

instance : DecidableEq Value := fun left right =>
  if same : left.equalAt left.wireDepth right = true then
    isTrue ((left.equalAt_correct right left.wireDepth (Nat.le_refl _)).mp same)
  else isFalse (fun equality => same
    ((left.equalAt_correct right left.wireDepth (Nat.le_refl _)).mpr equality))

end LeanPoo.Prototype.Dynamic
