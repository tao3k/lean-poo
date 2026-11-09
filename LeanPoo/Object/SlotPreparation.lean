-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Prototype.SlotSpec

namespace LeanPoo.Object.SlotPreparation

namespace EffectfulAdmission

/-- Native method installation can itself dispatch a mutable HashTable method.
Model that effect explicitly rather than treating protocol absence as purity. -/
def sweep {State Protocol Entry Result Error : Type}
    (protocol : State → Option Protocol)
    (hook : Protocol → Entry → State → Except Error (Entry × State))
    (write : Entry → State → Except Error (Result × State)) :
    List Entry → State → Except Error (List Result × State)
  | [], state => .ok ([], state)
  | entry :: rest, state => do
    let (selected, beforeWrite) ← match protocol state with
      | none => .ok (entry, state)
      | some selected => hook selected entry state
    let (result, afterWrite) ← write selected beforeWrite
    let (results, finalState) ← sweep protocol hook write rest afterWrite
    pure (result :: results, finalState)

def withoutHooks {State Entry Result Error : Type}
    (write : Entry → State → Except Error (Result × State)) :
    List Entry → State → Except Error (List Result × State)
  | [], state => .ok ([], state)
  | entry :: rest, state => do
    let (result, afterWrite) ← write entry state
    let (results, finalState) ← withoutHooks write rest afterWrite
    pure (result :: results, finalState)

/-- Derive this frame from the actual native write route. It is not a caller
purity flag. Error results and successful final state remain exactly equal. -/
theorem without_hooks_exact {State Protocol Entry Result Error : Type}
    (protocol : State → Option Protocol)
    (hook : Protocol → Entry → State → Except Error (Entry × State))
    (write : Entry → State → Except Error (Result × State))
    (preserves : ∀ entry state result after,
      protocol state = none → write entry state = .ok (result, after) →
      protocol after = none)
    (entries : List Entry) (state : State) (closed : protocol state = none) :
    sweep protocol hook write entries state = withoutHooks write entries state := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [sweep, closed, withoutHooks, Except.bind, Bind.bind]
    cases result : write entry state with
    | error cause => rfl
    | ok accepted =>
      rcases accepted with ⟨value, after⟩
      dsimp only
      rw [ih after (preserves entry state value after closed result)]

private def changingProtocol (state : Nat) : Option Unit :=
  if state = 0 then none else some ()

private def insertingWrite (entry state : Nat) : Except Unit (Nat × Nat) :=
  .ok (entry, state + 1)

private def observingHook (_ : Unit) (entry state : Nat) : Except Unit (Nat × Nat) :=
  .ok (entry + 100, state)

/-- A write installs a protocol between two slots. Initial absence alone
cannot justify hoisting selection out of the native installation loop. -/
theorem initial_absence_is_insufficient :
    changingProtocol 0 = none ∧
    sweep changingProtocol observingHook insertingWrite [0, 0] 0 ≠
      withoutHooks insertingWrite [0, 0] 0 := by
  change (none : Option Unit) = none ∧
    (Except.ok ([0, 100], 2) : Except Unit (List Nat × Nat)) ≠ .ok ([0, 0], 2)
  constructor
  · rfl
  · intro same
    cases same

end EffectfulAdmission
-- In the absence of a protocol, the old per-slot C4 walk visits the complete
-- receiver precedence list. The stock lane makes that same check once.
def stockProtocolVisits (precedence slots : Nat) : Nat :=
  if slots = 0 then 0 else precedence

theorem stock_protocol_visits_bound (precedence slots : Nat) :
    stockProtocolVisits precedence slots ≤ slots * precedence := by
  cases slots with
  | zero => simp [stockProtocolVisits]
  | succ n => simp [stockProtocolVisits, Nat.succ_mul]


end LeanPoo.Object.SlotPreparation

