import LeanPoo.Prototype.DynamicDescriptorSemantics

/-! Every finite declarative membership derivation is recognized at all
sufficiently large depths, including recursive named types and unions. -/
namespace LeanPoo.Prototype.Dynamic

private theorem uniform_bound (values : List α) (property : α → Nat → Prop)
    (members : ∀ value ∈ values, ∃ bound, ∀ fuel, bound ≤ fuel → property value fuel) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ value ∈ values, property value fuel := by
  induction values with
  | nil => exact ⟨0, by simp⟩
  | cons head tail ih =>
    obtain ⟨first, headAt⟩ := members head (by simp)
    obtain ⟨rest, tailAt⟩ := ih (fun value member => members value (by simp [member]))
    refine ⟨max first rest, ?_⟩
    intro fuel bound value member
    rcases List.mem_cons.mp member with same | member
    · subst value; exact headAt fuel (by omega)
    · exact tailAt fuel (by omega) value member

private theorem mapM_true (values : List α) (check : α → Except Error Bool)
    (members : ∀ value ∈ values, check value = .ok true) :
    values.mapM check = .ok (List.replicate values.length true) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    have headAt := members head (by simp)
    have tailAt := ih (fun value member => members value (by simp [member]))
    simp [headAt, tailAt, bind, Except.bind, pure, Except.pure, List.replicate_succ]

private theorem allM_true_of_members (values : List α) (check : α → Except Error Bool)
    (members : ∀ value ∈ values, check value = .ok true) :
    (do let results ← values.mapM check; pure (results.all id)) = .ok true := by
  simp [mapM_true values check members, bind, Except.bind, pure, Except.pure]

/-- Membership proofs are finite even for recursively registered contracts.
A successful union branch remains sufficient when the other is unresolved. -/
theorem accepts_complete (member : Accepted registry contract value) :
    ∃ bound, ∀ fuel, bound ≤ fuel → accepts registry fuel contract value = .ok true := by
  induction member with
  | top => exact ⟨1, fun fuel bound => by cases fuel with | zero => omega | succ => rfl⟩
  | unit => exact ⟨1, fun fuel bound => by cases fuel with | zero => omega | succ => rfl⟩
  | boolean => exact ⟨1, fun fuel bound => by cases fuel with | zero => omega | succ => rfl⟩
  | integer => exact ⟨1, fun fuel bound => by cases fuel with | zero => omega | succ => rfl⟩
  | integerRange lowerBound upperBound =>
    exact ⟨1, fun fuel bound => by cases fuel with
      | zero => omega
      | succ => simp [accepts, lowerBound, upperBound]⟩
  | text => exact ⟨1, fun fuel bound => by cases fuel with | zero => omega | succ => rfl⟩
  | @list values element members ih =>
    obtain ⟨budget, recognizes⟩ := uniform_bound values
      (fun value fuel => accepts registry fuel element value = .ok true) ih
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => exact allM_true_of_members values _ (recognizes fuel (by omega))
  | @dictionary entries key value keys values keyIH valueIH =>
    let check := fun fuel (entry : Value × Value) => do
      let keyOk ← accepts registry fuel key entry.1
      let valueOk ← accepts registry fuel value entry.2
      return keyOk && valueOk
    have each : ∀ entry ∈ entries, ∃ budget, ∀ fuel, budget ≤ fuel → check fuel entry = .ok true := by
      intro entry member
      obtain ⟨keyBudget, keyAt⟩ := keyIH entry member
      obtain ⟨valueBudget, valueAt⟩ := valueIH entry member
      refine ⟨max keyBudget valueBudget, ?_⟩
      intro fuel bound
      simp [check, keyAt fuel (by omega), valueAt fuel (by omega),
        bind, Except.bind, pure, Except.pure]
    obtain ⟨budget, recognizes⟩ := uniform_bound entries (fun entry fuel => check fuel entry = .ok true) each
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => exact allM_true_of_members entries (check fuel) (recognizes fuel (by omega))
  | @object slots fields present members ih =>
    let check : Nat → (String × Contract) → Except Error Bool := fun fuel slot => do
      let some value := (fields.find? (fun entry : String × Value => entry.1 == slot.1)).map Prod.snd |
        return false
      accepts registry fuel slot.2 value
    have each : ∀ slot ∈ slots, ∃ budget, ∀ fuel, budget ≤ fuel → check fuel slot = .ok true := by
      intro slot member
      cases found : (fields.find? (fun entry => entry.1 == slot.1)).map Prod.snd with
      | none => have presentAt := present slot member; simp [found] at presentAt
      | some value =>
        obtain ⟨budget, recognizes⟩ := ih slot member value found
        exact ⟨budget, fun fuel bound => by simpa [check, found] using recognizes fuel bound⟩
    obtain ⟨budget, recognizes⟩ := uniform_bound slots (fun slot fuel => check fuel slot = .ok true) each
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      change (do let results ← slots.mapM (check fuel); pure (results.all id)) = .ok true
      exact allM_true_of_members slots (check fuel) (recognizes fuel (by omega))
  | function registered =>
    exact ⟨1, fun fuel bound => by cases fuel with
      | zero => omega
      | succ => simpa [accepts] using registered⟩
  | descriptor registered =>
    exact ⟨1, fun fuel bound => by cases fuel with
      | zero => omega
      | succ => simpa [accepts] using registered⟩
  | named found member ih =>
    obtain ⟨budget, recognizes⟩ := ih
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => simpa [accepts, found] using recognizes fuel (by omega)
  | unionLeft member ih =>
    obtain ⟨budget, recognizes⟩ := ih
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [accepts]
      apply (unionResult_true _ _).mpr
      exact .inl (recognizes fuel (by omega))
  | unionRight member ih =>
    obtain ⟨budget, recognizes⟩ := ih
    refine ⟨budget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [accepts]
      apply (unionResult_true _ _).mpr
      exact .inr (recognizes fuel (by omega))
  | intersection leftMember rightMember leftIH rightIH =>
    obtain ⟨leftBudget, leftAt⟩ := leftIH
    obtain ⟨rightBudget, rightAt⟩ := rightIH
    refine ⟨max leftBudget rightBudget + 1, ?_⟩
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [accepts, leftAt fuel (by omega), rightAt fuel (by omega), bind, Except.bind]

theorem accepted_iff_recognized (registry : Registry) (contract : Contract) (value : Value) :
    Accepted registry contract value ↔ ∃ fuel, accepts registry fuel contract value = .ok true := by
  constructor
  · intro member
    obtain ⟨budget, recognizes⟩ := accepts_complete member
    exact ⟨budget, recognizes budget (Nat.le_refl _)⟩
  · rintro ⟨fuel, found⟩
    exact accepts_sound registry fuel contract value found

end LeanPoo.Prototype.Dynamic
