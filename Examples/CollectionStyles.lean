import LeanPoo.Functional.TableStyle

/-! Receiver-bound service revisions advance the collection proposal's future
work. Functions are immutable opaque payloads, never compared or rewrapped. -/
namespace LeanPoo.Examples.CollectionStyles
open Functional.OrderedDictionary

/-- One admitted service row contains its budget and an already checked callback. -/
abbrev Ledger := Nat × (Nat → Nat)

/-- A pure revision changes the budget, preserving the exact callback. -/
def revise (budget : Nat) (before : Ledger) : Except String Ledger :=
  if budget ≤ before.1 then .ok (budget, before.2) else .error "budget exceeded"

/-- The shared callback is opaque to the style engine. -/
def callback (value : Nat) : Nat := value + 1

/-- The original posh receiver is a persistent view of a checked service. -/
def before : TableReceiver Ledger := ⟨7, .posh, 10, some (100, callback)⟩

/-- Posh revision leaves its predecessor available with the same Function. -/
example : receiverStep before 11 (revise 80) =
    (before, .ok ⟨7, .posh, 11, some (80, callback)⟩) := by
  exact receiverStep_posh 7 10 11 (100, callback) (80, callback) (revise 80) (by simp [revise])

/-- The same revision in classy keeps the receiver identity and callback. -/
example : receiverStep ⟨7, .classy, 12, some (100, callback)⟩ 99 (revise 80) =
    (⟨7, .classy, 12, some (80, callback)⟩,
     .ok ⟨7, .classy, 12, some (80, callback)⟩) := by
  exact receiverStep_classy 7 12 99 (100, callback) (80, callback) (revise 80) (by simp [revise])

/-- A refused update retains the whole receiver and the original failure cause. -/
example : receiverStep before 11 (revise 120) =
    (before, .error (.callback "budget exceeded")) := by
  apply receiverStep_failure before 11 (100, callback) (revise 120) "budget exceeded" rfl
  simp [revise]

/-- Failed target construction cannot consume a live linear source. -/
example : prepareStyleConvert (.passing .linear) (some (80, callback))
    (fun _ => (Except.error "presentation refused" : Except String Ledger)) =
      (some (80, callback), .error (.callback "presentation refused")) := rfl

/-- Retrying that source with a complete classy result transfers the same Function. -/
example : prepareStyleConvert (E := String) (.passing .linear) (some (80, callback))
    (fun row => .ok (TablePresentation.receiver .classy, row)) =
      (none, .ok (.receiver .classy, (80, callback))) := rfl

/-- Competing installation wins once; a stale receiver cannot overwrite it. -/
example : installStyle (E := String) ReceiverStyle.classy.base
    ⟨3, some (80, callback)⟩ 2 (50, callback) =
      (⟨3, some (80, callback)⟩, .error .stale) :=
  receiver_install_stale .classy _ 2 _ (by decide)

/-- Reverse transfer recovers the exact pure snapshot and retires classy aliases. -/
example : prepareStyleConvert (E := String) (.receiver .classy) (some (80, callback))
    (fun row => .ok (TablePresentation.receiver .posh, row)) =
      (none, .ok (.receiver .posh, (80, callback))) := rfl

end LeanPoo.Examples.CollectionStyles
