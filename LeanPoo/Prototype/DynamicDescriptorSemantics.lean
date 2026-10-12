import LeanPoo.Prototype.DynamicDescriptor

/-! Declarative dynamic membership and checked-call admission. -/
namespace LeanPoo.Prototype.Dynamic

inductive Accepted (registry : Registry) : Contract → Value → Prop where
  | top : Accepted registry .top value
  | unit : Accepted registry .unit .unit
  | boolean : Accepted registry .boolean (.boolean value)
  | integer : Accepted registry .integer (.integer value)
  | integerRange (lowerBound : lower ≤ value) (upperBound : value ≤ upper) :
      Accepted registry (.integerRange lower upper) (.integer value)
  | text : Accepted registry .text (.text value)
  | list (members : ∀ value ∈ values, Accepted registry element value) :
      Accepted registry (.listOf element) (.list values)
  | dictionary (keys : ∀ entry ∈ entries, Accepted registry key entry.1)
      (values : ∀ entry ∈ entries, Accepted registry value entry.2) :
      Accepted registry (.dictionaryOf key value) (.dictionary entries)
  | object (present : ∀ slot ∈ slots,
      ((fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd).isSome = true)
      (members : ∀ slot ∈ slots, ∀ value,
        (fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd = some value →
        Accepted registry slot.2 value) : Accepted registry (.objectOf slots) (.object fields)
  | function {id : String} (registered : (registry.function? id).isSome = true) :
      Accepted registry (.functionOf input output) (.function id)
  | descriptor {id : String} (registered : (registry.descriptor? id).isSome = true) :
      Accepted registry .descriptor (.descriptor id)
  | named {id : String} (found : registry.descriptor? id = some descriptor)
      (member : Accepted registry descriptor.contract value) :
      Accepted registry (.named id) value
  | unionLeft (member : Accepted registry left value) :
      Accepted registry (.union left right) value
  | unionRight (member : Accepted registry right value) :
      Accepted registry (.union left right) value
  | intersection (leftMember : Accepted registry left value)
      (rightMember : Accepted registry right value) :
      Accepted registry (.intersection left right) value

private theorem allM_true (values : List α) (check : α → Except Error Bool)
    (checks : List Bool) (success : values.mapM check = .ok checks)
    (all : checks.all id = true) : ∀ value ∈ values, check value = .ok true := by
  induction values generalizing checks with
  | nil => simp
  | cons value rest ih =>
    simp only [List.mapM_cons] at success
    cases first : check value with
    | error err => simp [first, bind, Except.bind] at success
    | ok checked =>
      cases tail : rest.mapM check with
      | error err => simp [first, tail, bind, Except.bind] at success
      | ok remaining =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at success
        subst checks
        have both : checked = true ∧ remaining.all id = true := by simpa using all
        have headTrue : checked = true := both.1
        have restTrue : remaining.all id = true := both.2
        intro query member
        simp only [List.mem_cons] at member
        rcases member with same | member
        · subst query; simpa [headTrue] using first
        · exact ih remaining tail restTrue query member

/-- Membership success is admitted against the declarative contract relation,
including nested objects, dictionaries, named types and descriptors themselves. -/
theorem accepts_sound (registry : Registry) (fuel : Nat) (contract : Contract) (value : Value)
    (success : accepts registry fuel contract value = .ok true) : Accepted registry contract value := by
  induction fuel generalizing contract value with
  | zero => simp [accepts] at success
  | succ fuel ih =>
    cases contract with
    | top => exact .top
    | bottom => simp [accepts] at success
    | unit => cases value <;> simp [accepts] at success; exact .unit
    | boolean => cases value <;> simp [accepts] at success; exact .boolean
    | integer => cases value <;> simp [accepts] at success; exact .integer
    | integerRange lower upper =>
      cases value <;> simp [accepts] at success
      exact .integerRange success.1 success.2
    | text => cases value <;> simp [accepts] at success; exact .text
    | functionOf input output =>
      cases value <;> simp [accepts] at success
      exact .function success
    | descriptor =>
      cases value <;> simp [accepts] at success
      exact .descriptor success
    | listOf element =>
      cases value <;> simp only [accepts, Except.ok.injEq, Bool.false_eq_true] at success
      rename_i values
      cases checks : values.mapM (accepts registry fuel element) with
      | error err => simp [checks, bind, Except.bind] at success
      | ok results =>
        have all : results.all id = true := by
          simpa [checks, bind, Except.bind, pure, Except.pure] using success
        exact .list (fun value member => ih element value (allM_true values _ results checks all value member))
    | dictionaryOf key val =>
      cases value <;> simp only [accepts, Except.ok.injEq, Bool.false_eq_true] at success
      rename_i entries
      let check := fun entry : Value × Value => do
        let k ← accepts registry fuel key entry.1
        let v ← accepts registry fuel val entry.2
        return k && v
      cases checks : entries.mapM check with
      | error err =>
        change (do let checks ← entries.mapM check; pure (checks.all id)) = .ok true at success
        simp [checks, bind, Except.bind] at success
      | ok results =>
        have all : results.all id = true := by
          change (do let checks ← entries.mapM check; pure (checks.all id)) = .ok true at success
          simpa [checks, bind, Except.bind, pure, Except.pure] using success
        have members : ∀ entry ∈ entries,
            Accepted registry key entry.1 ∧ Accepted registry val entry.2 := by
          intro entry member
          have both := allM_true entries check results checks all entry member
          dsimp [check] at both
          cases k : accepts registry fuel key entry.1 with
          | error err => simp [k, bind, Except.bind] at both
          | ok keyOk =>
            cases v : accepts registry fuel val entry.2 with
            | error err => simp [k, v, bind, Except.bind] at both
            | ok valueOk =>
              have trueBoth : keyOk = true ∧ valueOk = true := by
                simpa [k, v, bind, Except.bind, pure, Except.pure] using both
              exact ⟨ih key entry.1 (by simpa [trueBoth.1] using k),
                ih val entry.2 (by simpa [trueBoth.2] using v)⟩
        exact .dictionary (fun entry member => (members entry member).1)
          (fun entry member => (members entry member).2)
    | objectOf slots =>
      cases value <;> simp only [accepts, Except.ok.injEq, Bool.false_eq_true] at success
      rename_i fields
      let check := fun slot : String × Contract =>
        match (fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd with
        | some value => accepts registry fuel slot.2 value
        | _ => pure false
      cases checks : slots.mapM check with
      | error err =>
        change (do let checks ← slots.mapM check; pure (checks.all id)) = .ok true at success
        simp [checks, bind, Except.bind] at success
      | ok results =>
        have all : results.all id = true := by
          change (do let checks ← slots.mapM check; pure (checks.all id)) = .ok true at success
          simpa [checks, bind, Except.bind, pure, Except.pure] using success
        have members : ∀ slot ∈ slots, ∃ value,
            (fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd = some value ∧
              Accepted registry slot.2 value := by
          intro slot member
          have checked := allM_true slots check results checks all slot member
          dsimp [check] at checked
          cases found : (fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd with
          | none => simp [found, pure, Except.pure] at checked
          | some value => exact ⟨value, rfl, ih slot.2 value (by simpa [found] using checked)⟩
        apply Accepted.object
        · intro slot member
          obtain ⟨value, found, accepted⟩ := members slot member
          simp [found]
        · intro slot member value found
          obtain ⟨expected, same, accepted⟩ := members slot member
          have equalValue : expected = value := Option.some.inj (same.symm.trans found)
          simpa [equalValue] using accepted
    | named identity =>
      simp only [accepts] at success
      cases found : registry.descriptor? identity with
      | none => simp only [found] at success; contradiction
      | some descriptor =>
        simp only [found] at success
        exact .named found (ih _ _ success)
    | union left right =>
      simp only [accepts] at success
      cases checked : accepts registry fuel left value with
      | error err => simp [checked, bind, Except.bind] at success
      | ok yes =>
        cases yes
        · simp [checked, bind, Except.bind] at success
          exact .unionRight (ih _ _ success)
        · exact .unionLeft (ih _ _ checked)
    | intersection left right =>
      simp only [accepts] at success
      cases checked : accepts registry fuel left value with
      | error err => simp [checked, bind, Except.bind] at success
      | ok yes =>
        cases yes
        · simp [checked, bind, Except.bind, pure, Except.pure] at success
        · simp [checked, bind, Except.bind] at success
          exact .intersection (ih _ _ checked) (ih _ _ success)

/-- Every successful dynamic call checks both contracts around the actual
registered function invocation. -/
theorem Descriptor.call_sound (descriptor : Descriptor) (registry : Registry) (fuel : Nat)
    (input output : Contract) (contract : descriptor.contract = .functionOf input output)
    (identity : String) (argument result : Value)
    (success : descriptor.call registry fuel (.function identity) argument = .ok result) :
    Accepted registry input argument ∧ Accepted registry output result := by
  simp only [Descriptor.call, contract] at success
  cases found : registry.function? identity with
  | none => simp only [found] at success; contradiction
  | some callable =>
    simp only [found] at success
    cases checked : Dynamic.accepts registry fuel input argument with
    | error err => simp [checked, bind, Except.bind] at success
    | ok yes =>
      cases yes
      · simp [checked, bind, Except.bind, pure, Except.pure] at success
      · cases called : callable argument with
        | error err => simp [checked, called, bind, Except.bind] at success
        | ok value =>
          cases outputChecked : Dynamic.accepts registry fuel output value with
          | error err => simp [checked, called, outputChecked, bind, Except.bind] at success
          | ok yes =>
            cases yes
            · simp [checked, called, outputChecked, bind, Except.bind, pure, Except.pure] at success
            · simp [checked, called, outputChecked, bind, Except.bind, pure, Except.pure] at success
              subst result
              exact ⟨accepts_sound _ _ _ _ checked, accepts_sound _ _ _ _ outputChecked⟩

end LeanPoo.Prototype.Dynamic
