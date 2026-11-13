-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.SlotContracts

-- State includes observations and effects. Failure keeps the resulting state.
abbrev Action (S E A : Type) := S → Except E A × S

def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error err, after) => (.error err, after)
    | (.ok value, after) => next value after

def pureAction (value : A) : Action S E A :=
  fun state => (.ok value, state)

-- Ordinary Slot checking keeps presence, demand, then the value predicate.
-- Presence and demand may observe reads or dispatch the receiver's protocol.
def slot (present : K → Action S E Bool) (demand : K → Action S E V)
    (name : K) (check : V → Action S E Bool) : Action S E Bool :=
  bind (present name) fun found =>
    if found then bind (demand name) check else pureAction false

def chain (first rest : Action S E Bool) : Action S E Bool :=
  bind first fun passed => if passed then rest else pureAction false

def parallelLists (test : K → P → Action S E Bool) :
    List K → List P → Action S E Bool
  | name :: names, check :: checks =>
    chain (test name check) (parallelLists test names checks)
  | _, _ => pureAction true

def declaredFields (test : K → P → Action S E Bool) :
    List (K × P) → Action S E Bool
  | [] => pureAction true
  | (name, check) :: rest => chain (test name check) (declaredFields test rest)

theorem declarations_preserve_outcome_and_effects (test : K → P → Action S E Bool)
    (fields : List (K × P)) :
    declaredFields test fields =
      parallelLists test (fields.map Prod.fst) (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨name, check⟩
    simp only [declaredFields, List.map_cons, parallelLists, ih]

theorem failed_field_skips_rest (first rest : Action S E Bool) (before after : S)
    (failed : first before = (.ok false, after)) :
    chain first rest before = (.ok false, after) := by
  simp [chain, bind, pureAction, failed]

theorem absent_slot_preserves_presence_effect (present : K → Action S E Bool)
    (demand : K → Action S E V) (name : K) (check : V → Action S E Bool)
    (before after : S) (absent : present name before = (.ok false, after)) :
    slot present demand name check before = (.ok false, after) := by
  simp [slot, bind, pureAction, absent]

-- The storage route must already be admitted. A missing or cold cell has no
-- stored value; a stored Scheme false is still a present value.
def storedSlot (admitted : Bool) (stored : Option V) (check : V → Bool) : Bool :=
  admitted && (stored.map check).getD false

theorem refused_route_skips_check (stored : Option V) (check : V → Bool) :
    storedSlot false stored check = false := rfl

theorem stored_false_is_present :
    storedSlot true (some false) (! ·) = true := rfl

theorem uncomputed_cell_is_not_a_value (check : V → Bool) :
    storedSlot true (none : Option V) check = false := rfl

-- Even a warm admitted cell can issue an observable semantic read.
example :
    slot (fun (_ : Unit) => pureAction true)
      (fun _ (reads : Nat) => (.ok false, reads + 1))
      () (fun value => pureAction (!value)) 0 =
      ((.ok true : Except Unit Bool), 1) := rfl

-- Cold storage refusal does not determine the ordinary contract outcome.
example :
    storedSlot true (none : Option Bool) id = false ∧
    slot (fun (_ : Unit) => pureAction true)
      (fun _ (reads : Nat) => (.ok true, reads + 1))
      () pureAction 0 = ((.ok true : Except Unit Bool), 1) := by
  exact ⟨rfl, rfl⟩

end LeanPoo.Object.SlotContracts
