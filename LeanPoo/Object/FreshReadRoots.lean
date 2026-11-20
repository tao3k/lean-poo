-- SPDX-FileCopyrightText: 2026 tao3k team and Contributors
-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.Parameters
import LeanPoo.Object.SlotObservation

/- Fresh root collection, not rewriting a previously signed dependency list.
   Read is an exact issued-record identity, not an owner, slot name or value.
   State can include the complete selected preorder and first refusal state. -/
namespace LeanPoo.Object.FreshReadRoots
open LeanPoo.Functional.Parameters
variable {Read State Error Value : Type} [DecidableEq Read]

def run (visit : Read → State → Except Error State) (roots : List Read) (state : State) :
    Except Error State := roots.foldlM (fun current root => visit root current) state

omit [DecidableEq Read] in
theorem run_cons (visit : Read → State → Except Error State) (root : Read)
    (rest : List Read) (state : State) :
    run visit (root :: rest) state = (visit root state).bind (run visit rest) := rfl

/-- A visited-record selector keeps its complete result and first refusal.
    Its existing DFS may discover other roots through dependencies. No
    commutativity of visits or observer effects is assumed. -/
theorem normalized_run (visit : Read → State → Except Error State)
    (marked : State → Read → Prop)
    (skip : ∀ state root, marked state root → visit root state = .ok state)
    (mark : ∀ state root next, visit root state = .ok next → marked next root)
    (grow : ∀ state root next, visit root state = .ok next →
      ∀ prior, marked state prior → marked next prior)
    (roots history : List Read) (state : State)
    (prior : ∀ root, root ∈ history → marked state root) :
    run visit (uniqueBindings id history roots) state = run visit roots state := by
  induction roots generalizing history state with
  | nil => rfl
  | cons root rest ih =>
    by_cases present : root ∈ history
    · have already := skip state root (prior root present)
      simpa only [uniqueBindings, id_eq, ite_eq_left present, run_cons, already, Except.bind]
        using ih history state prior
    · cases step : visit root state with
      | error cause => simp [uniqueBindings, present, run_cons, step, Except.bind]
      | ok next =>
        have continued : ∀ item, item ∈ root :: history → marked next item := by
          intro item member
          rcases List.mem_cons.mp member with equal | earlier
          · subst item; exact mark state root next step
          · exact grow state root next step item (prior item earlier)
        simpa only [uniqueBindings, id_eq, ite_eq_right present, run_cons, step, Except.bind]
          using ih (root :: history) next continued

theorem fresh_roots_preserve_selection (visit : Read → State → Except Error State)
    (marked : State → Read → Prop)
    (skip : ∀ state root, marked state root → visit root state = .ok state)
    (mark : ∀ state root next, visit root state = .ok next → marked next root)
    (grow : ∀ state root next, visit root state = .ok next →
      ∀ prior, marked state prior → marked next prior)
    (roots : List Read) (state : State) :
    run visit (uniqueBindings id [] roots) state = run visit roots state :=
  normalized_run visit marked skip mark grow roots [] state (by simp)

theorem root_count_bound (roots history : List Read) :
    (uniqueBindings id history roots).length ≤ roots.length := by
  induction roots generalizing history with
  | nil => simp [uniqueBindings]
  | cons root rest ih =>
    by_cases present : root ∈ history
    · simpa [uniqueBindings, present] using Nat.le_trans (ih history) (Nat.le_succ rest.length)
    · simpa [uniqueBindings, present] using Nat.succ_le_succ (ih (root :: history))

structure Capture (Read Error Value : Type) where
  outcome : Except Error Value
  roots : List Read
  events : List Read

def freshSupport (captured : Capture Read Error Value) : Capture Read Error Value :=
  { captured with roots := uniqueBindings id [] captured.roots }

theorem original_outcome (captured : Capture Read Error Value) :
    (freshSupport captured).outcome = captured.outcome := rfl

theorem every_delivery_preserved (captured : Capture Read Error Value) :
    (freshSupport captured).events = captured.events := rfl

/-- Entry and return remain separate checks with an arbitrary intervening
    effect. Equality of root selection never grants reuse of an approval. -/
def around {World : Type} (check : World → Except Error Unit)
    (effect : World → Except Error World) (world : World) : Except Error World := do
  check world
  let next ← effect world
  check next
  pure next

theorem independent_boundaries {World : Type} (reference optimized : World → Except Error Unit)
    (same : ∀ world, optimized world = reference world)
    (effect : World → Except Error World) (world : World) :
    around optimized effect world = around reference effect world := by
  have equal : optimized = reference := funext same
  rw [equal]

example (roots events : List Nat) :
    (freshSupport (⟨.error false, roots, events⟩ : Capture Nat Bool Nat)).outcome = .error false := rfl

example : around (fun valid : Bool => if valid then .ok () else .error "stale")
    (fun _ => .ok false) true = .error "stale" := rfl

#guard uniqueBindings id [] ([10, 20, 10, 30, 20] : List Nat) = [10, 20, 30]
-- Distinct issued identities remain distinct even if their owner and slot coincide.
#guard uniqueBindings id [] ([0, 1] : List Nat) = [0, 1]

end LeanPoo.Object.FreshReadRoots
