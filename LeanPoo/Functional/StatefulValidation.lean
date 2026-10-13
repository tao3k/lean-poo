import LeanPoo.Functional.Validation

/-! Ordered validation with explicit returned state on both success and failure.
The first failing step retains its state; later steps are not applied. -/
namespace LeanPoo.Functional.Validation
universe u v w x y
variable {State : Type u} {Input : Type v} {Output : Type w} {Error : Type x}

def traverseState (check : State → Input → Except Error Output × State)
    (state : State) : List Input → Except Error (List Output) × State
  | [] => (.ok [], state)
  | item :: rest =>
    let (outcome, next) := check state item
    match outcome with
    | .error error => (.error error, next)
    | .ok value =>
      let (remaining, final) := traverseState check next rest
      (remaining.map (value :: ·), final)

theorem traverseState_append (check : State → Input → Except Error Output × State)
    (state : State) (left right : List Input) :
    traverseState check state (left ++ right) =
      match traverseState check state left with
      | (.error error, final) => (.error error, final)
      | (.ok before, next) =>
        let (after, final) := traverseState check next right
        (after.map (before ++ ·), final) := by
  induction left generalizing state with
  | nil =>
    simp only [List.nil_append, traverseState]
    cases traverseState check state right with
    | mk outcome final => cases outcome <;> rfl
  | cons item rest ih =>
    cases first : check state item with
    | mk outcome next =>
      cases outcome with
      | error error => simp [traverseState, first]
      | ok value =>
        simp only [List.cons_append, traverseState, first]
        rw [ih]
        cases traverseState check next rest with
        | mk outcome final =>
          cases outcome with
          | error error => rfl
          | ok values =>
            simp only [Except.map]
            cases traverseState check final right with
            | mk remaining last => cases remaining <;> rfl

/-- The final state is exactly the failing step's returned state, after a wholly
successful prefix. No partial output list is published. The suffix is arbitrary. -/
theorem traverseState_error_iff (check : State → Input → Except Error Output × State)
    (state : State) (items : List Input) (error : Error) (final : State) :
    traverseState check state items = (.error error, final) ↔
      ∃ before item after values next, items = before ++ item :: after ∧
        traverseState check state before = (.ok values, next) ∧
        check next item = (.error error, final) := by
  constructor
  · induction items generalizing state with
    | nil => simp [traverseState]
    | cons item rest ih =>
      intro failed
      cases first : check state item with
      | mk outcome next =>
        cases outcome with
        | error e =>
          have equal : ((Except.error e : Except Error (List Output)), next) = (Except.error error, final) := by
            simpa [traverseState, first] using failed
          have sameError : e = error := Except.error.inj (congrArg Prod.fst equal)
          have sameState : next = final := congrArg Prod.snd equal
          subst e; subst next
          exact ⟨[], item, rest, [], state, rfl, rfl, first⟩
        | ok value =>
          have tail : traverseState check next rest = (.error error, final) := by
            cases second : traverseState check next rest with
            | mk outcome last => cases outcome <;> simp_all [traverseState, Except.map]
          obtain ⟨before, bad, after, values, middle, split, good, failure⟩ := ih next tail
          exact ⟨item :: before, bad, after, value :: values, middle,
            by simp [split], by simp [traverseState, first, good, Except.map], failure⟩
  · rintro ⟨before, item, after, values, next, rfl, good, failed⟩
    rw [traverseState_append, good]
    simp [traverseState, failed, Except.map]

/-- Stateless validation is the state-preserving special case. -/
theorem traverseState_stateless (check : Input → Except Error Output) (state : State) (items : List Input) :
    traverseState (fun state item => (check item, state)) state items = (traverse check items, state) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [traverseState, traverse]
    cases check item <;> simp [ih, Except.bind, Except.map]

/-- A commuting input adapter preserves the complete outcome and returned state. -/
theorem traverseState_map {Other : Type y}
    (check : State → Other → Except Error Output × State) (adapt : Input → Other)
    (state : State) (items : List Input) :
    traverseState check state (items.map adapt) =
      traverseState (fun state item => check state (adapt item)) state items := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.map_cons, traverseState]
    cases check state (adapt item) with
    | mk outcome next => cases outcome <;> simp [ih]

/-- A step invariant survives the complete batch, including a refusing step's
returned state. The invariant is independent of the output/error carrier. -/
theorem traverseState_invariant (check : State → Input → Except Error Output × State)
    (invariant : State → Prop)
    (preserves : ∀ state item, invariant state → invariant (check state item).2)
    (state : State) (valid : invariant state) (items : List Input) :
    invariant (traverseState check state items).2 := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih =>
    have next := preserves state item valid
    cases first : check state item with
    | mk outcome retained =>
      rw [first] at next
      cases outcome with
      | error error => simpa [traverseState, first] using next
      | ok value =>
        have final := ih retained next
        cases remaining : traverseState check retained rest with
        | mk output last => simpa [traverseState, first, remaining] using final

end LeanPoo.Functional.Validation
