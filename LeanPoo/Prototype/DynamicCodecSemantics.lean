import LeanPoo.Prototype.DynamicCodec
import Std.Data.String.ToInt

/-! Structural wire inversion for every dynamic value, including arbitrary
nested values, exact integers and ordered duplicate entries. -/
namespace LeanPoo.Prototype.Dynamic

private theorem mapM_encoded (values : List α) (encode : α → β)
    (decode : β → Except ε α)
    (roundTrip : ∀ value ∈ values, decode (encode value) = .ok value) :
    (values.map encode).mapM decode = .ok values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    have first := roundTrip head (by simp)
    have rest := ih (fun value member => roundTrip value (by simp [member]))
    simp [first, rest, bind, Except.bind, pure, Except.pure]

/-- The bound is recursive value depth, independent of payload size.
No registry assumptions are needed for raw structural reconstruction. -/
theorem Value.decodeJson_encodeJson (value : Value) (fuel : Nat)
    (bound : value.wireDepth ≤ fuel) : Value.decodeJson fuel value.encodeJson = .ok value := by
  cases fuel with
  | zero => have positive := value.wireDepth_pos; omega
  | succ fuel =>
    cases shape : value with
    | unit => simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | boolean value => simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | integer value =>
      simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | text value => simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | function identity => simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | descriptor identity => simp [Value.encodeJson, Value.decodeJson, pure, Except.pure]
    | list values =>
      have children : ∀ child ∈ values, Value.decodeJson fuel child.encodeJson = .ok child := by
        intro child member
        have smaller := List.sizeOf_lt_of_mem member
        have parent : sizeOf child < sizeOf (Value.list values) := by simp_all; omega
        have height := List.le_max?_getD_of_mem (k := 0)
          (List.mem_map_of_mem (f := Value.wireDepth) member)
        exact Value.decodeJson_encodeJson child fuel (by simp_all [Value.wireDepth]; omega)
      have decoded := mapM_encoded values Value.encodeJson (Value.decodeJson fuel) children
      simp [Value.encodeJson, Value.decodeJson, decoded, bind, Except.bind, pure, Except.pure]
    | dictionary entries =>
      have children : ∀ entry ∈ entries,
          Value.decodeJson fuel entry.1.encodeJson = .ok entry.1 ∧
          Value.decodeJson fuel entry.2.encodeJson = .ok entry.2 := by
        intro entry member
        have smaller := List.sizeOf_lt_of_mem member
        cases entry with
        | mk key value =>
          have keySmaller : sizeOf key < sizeOf (Value.dictionary entries) := by simp_all; omega
          have valueSmaller : sizeOf value < sizeOf (Value.dictionary entries) := by simp_all; omega
          have height := List.le_max?_getD_of_mem (k := 0)
            (List.mem_map_of_mem (f := fun entry : Value × Value =>
              max entry.1.wireDepth entry.2.wireDepth) member)
          exact ⟨Value.decodeJson_encodeJson key fuel (by simp_all [Value.wireDepth]; omega),
            Value.decodeJson_encodeJson value fuel (by simp_all [Value.wireDepth]; omega)⟩
      have decoded := mapM_encoded entries
        (fun entry => Lean.Json.arr #[entry.1.encodeJson, entry.2.encodeJson])
        (decodeDictionaryEntry (Value.decodeJson fuel))
        (by
          intro entry member
          obtain ⟨key, value⟩ := children entry member
          simp [decodeDictionaryEntry, key, value, bind, Except.bind, pure, Except.pure])
      simp only [Value.encodeJson, Value.decodeJson]
      rw [decoded]
      rfl
    | object entries =>
      have children : ∀ entry ∈ entries,
          Value.decodeJson fuel entry.2.encodeJson = .ok entry.2 := by
        intro entry member
        have smaller := List.sizeOf_lt_of_mem member
        cases entry with
        | mk key value =>
          have parent : sizeOf value < sizeOf (Value.object entries) := by simp_all; omega
          have height := List.le_max?_getD_of_mem (k := 0)
            (List.mem_map_of_mem (f := fun entry : String × Value => entry.2.wireDepth) member)
          exact Value.decodeJson_encodeJson value fuel (by simp_all [Value.wireDepth]; omega)
      have decoded := mapM_encoded entries
        (fun entry => Lean.Json.arr #[Lean.Json.str entry.1, entry.2.encodeJson])
        (decodeObjectEntry (Value.decodeJson fuel))
        (by
          intro entry member
          simp [decodeObjectEntry, children entry member, bind, Except.bind, pure, Except.pure])
      simp only [Value.encodeJson, Value.decodeJson]
      rw [decoded]
      rfl

termination_by sizeOf value
decreasing_by all_goals simp_all; all_goals omega

/-- A value admitted by this exact registry/descriptor round-trips through
the structural wire gate at every budget satisfying the nesting-depth bound. -/
theorem Descriptor.json_roundTrip (descriptor : Descriptor) (registry : Registry)
    (fuel : Nat) (value : Value) (admitted : Admitted registry descriptor.contract)
    (valid : descriptor.validate registry fuel value = .ok admitted)
    (bound : value.wireDepth ≤ fuel) :
    descriptor.encodeJson registry fuel value = .ok value.encodeJson ∧
      descriptor.decodeJson registry fuel value.encodeJson = .ok admitted := by
  have same := descriptor.validate_value registry fuel value admitted valid
  constructor
  · simp [Descriptor.encodeJson, valid, same, bind, Except.bind, pure, Except.pure]
  · simp [Descriptor.decodeJson, value.decodeJson_encodeJson fuel bound, valid,
      bind, Except.bind]

end LeanPoo.Prototype.Dynamic
