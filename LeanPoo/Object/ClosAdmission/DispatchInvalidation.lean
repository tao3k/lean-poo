-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.PublishedDispatch
import LeanPoo.Functional.OrderedReachability

/-! The existing reverse index is over dependency rows, oriented consumer
to provider in Lean. In the published-plan model the edge goes from the
provider to the dependent. Transposing the certified rows relates the two. -/
namespace LeanPoo.Object.ClosAdmission.DispatchInvalidation
open LeanPoo.Functional.StrongComponents (Reach)
open LeanPoo.Functional.LocalSccRegion (Edge Region Same restricted)
open LeanPoo.Functional.OrderedReachability (affectedBy affected_dependency_rewrite)
open LeanPoo.Object.ClosAdmission.PublishedDispatch (Affected advanceEpoch)

def envelope {n : Nat} (old next : Edge n) : Edge n :=
  fun consumer provider => old consumer provider || next consumer provider

theorem affected_transpose {n : Nat} (rows : Edge n) (dirty : Fin n → Prop) (owner : Fin n) :
    affectedBy rows dirty owner ↔ Affected (fun source reader => rows reader source) dirty owner := by
  constructor <;> rintro ⟨root, edited, path⟩
  · exact ⟨root, edited, path.reverse⟩
  · exact ⟨root, edited, path.reverse⟩

/-- The new rows and the SCC envelope agree on all consumers outside the
edit roots. Therefore the old inverse reaches exactly the closure needed
by the publication, including after additions, deletions and replacements. -/
theorem old_inverse_equals_envelope {n : Nat} (old next : Edge n) (dirty : Fin n → Prop)
    (unchanged : ∀ consumer, ¬ dirty consumer → ∀ provider,
      old consumer provider = next consumer provider) (owner : Fin n) :
    affectedBy old dirty owner ↔
      Affected (fun source reader => envelope old next reader source) dirty owner := by
  rw [← affected_transpose (envelope old next) dirty owner]
  apply affected_dependency_rewrite old (envelope old next) dirty _ owner
  intro consumer clean provider
  simp [envelope, unchanged consumer clean provider]

theorem epoch_changes_exactly_inverse {n : Nat} (old next : Edge n) (dirty : Fin n → Prop)
    (unchanged : ∀ consumer, ¬ dirty consumer → ∀ provider,
      old consumer provider = next consumer provider)
    (epoch : Fin n → Nat) (owner : Fin n) :
    advanceEpoch (fun source reader => envelope old next reader source) dirty epoch owner ≠
      epoch owner ↔ affectedBy old dirty owner := by
  classical
  rw [old_inverse_equals_envelope old next dirty unchanged owner]
  by_cases affected : Affected (fun source reader => envelope old next reader source) dirty owner <;>
    simp [advanceEpoch, affected]

theorem local_scc_membership_exact {n : Nat} (old next : Edge n) (dirty : Fin n → Prop)
    (unchanged : ∀ consumer, ¬ dirty consumer → ∀ provider,
      old consumer provider = next consumer provider)
    (a b : Fin n) :
    Same next a b ↔
      @ite Prop (Region (envelope old next) dirty a) (Classical.propDecidable _)
        (Same (restricted next (envelope old next) dirty) a b) (Same old a b) := by
  apply LeanPoo.Functional.LocalSccRegion.local_replacement_equals_cold
  · intro consumer provider member
    simp [envelope, member]
  · intro consumer provider member
    simp [envelope, member]
  · exact unchanged

/-- Consumers without a return path to them are invalidated too. Thus an
SCC repair region cannot be used as the full set of invalidated epochs. -/
theorem acyclic_consumers_still_invalidate {n : Nat} (rows : Edge n)
    (dirty : Fin n → Prop) (consumer provider : Fin n)
    (changed : dirty provider) (reads : Reach rows consumer provider)
    (noReturn : ∀ root, dirty root → ¬ Reach rows root consumer) :
    affectedBy rows dirty consumer ∧ ¬ Region rows dirty consumer := by
  refine ⟨⟨provider, changed, reads⟩, ?_⟩
  rintro ⟨⟨root, dirtyRoot, back⟩, _⟩
  exact noReturn root dirtyRoot back

/-- Reverse reachability is constant throughout a strongly connected
component. A component can propagate its epoch change as one unit. -/
theorem component_invalidation_uniform {n : Nat} (rows : Edge n)
    (dirty : Fin n → Prop) {a b : Fin n} (component : Same rows a b) :
    affectedBy rows dirty a ↔ affectedBy rows dirty b := by
  constructor <;> rintro ⟨root, seeded, path⟩
  · exact ⟨root, seeded, component.2.trans path⟩
  · exact ⟨root, seeded, component.1.trans path⟩

open LeanPoo.Object.ClosAdmission.PublishedDispatch
  (Stage World Published current cold prior_entry_valid_after_edit)

noncomputable def indexedEpoch {n : Nat} (rows : Edge n) (dirty : Fin n → Prop)
    (epoch : Fin n → Nat) (owner : Fin n) : Nat :=
  @ite Nat (affectedBy rows dirty owner) (Classical.propDecidable _)
    (epoch owner + 1) (epoch owner)

theorem indexed_epochs_refine_edit {n : Nat} (old next : Edge n) (dirty : Fin n → Prop)
    (unchanged : ∀ consumer, ¬ dirty consumer → ∀ provider,
      old consumer provider = next consumer provider) (epoch : Fin n → Nat) :
    indexedEpoch old dirty epoch =
      advanceEpoch (fun source reader => envelope old next reader source) dirty epoch := by
  classical
  funext owner
  have exactClosure := old_inverse_equals_envelope old next dirty unchanged owner
  by_cases affected : affectedBy old dirty owner
  · simp [indexedEpoch, advanceEpoch, affected, exactClosure.mp affected]
  · have clean : ¬ Affected (fun source reader => envelope old next reader source) dirty owner :=
      fun h => affected (exactClosure.mpr h)
    simp [indexedEpoch, advanceEpoch, affected, clean]

/-- A stamp from the existing reverse walk is enough to justify a retained
plan. The proof uses the captured input support and the exact logical set
of owners visited by the index, without a second dependency check on hit. -/
theorem retained_plan_after_indexed_edit {n : Nat} {old next : Edge n} {dirty : Fin n → Prop}
    (unchanged : ∀ consumer, ¬ dirty consumer → ∀ provider,
      old consumer provider = next consumer provider)
    (stage : Stage n Value Runtime Recipe Event Failure)
    (before after : World n Value Runtime) (entry : Published n Recipe)
    (past : entry.epoch ≤ before.epoch stage.owner)
    (sound : current stage before entry → entry.plan = cold stage before)
    (registered : ∀ source ∈ stage.support, Reach (envelope old next) stage.owner source)
    (input : ∀ source, ¬ dirty source → after.input source = before.input source)
    (installed : after.epoch = indexedEpoch old dirty before.epoch)
    (hit : current stage after entry) :
    entry.plan = cold stage after := by
  rw [indexed_epochs_refine_edit old next dirty unchanged] at installed
  exact prior_entry_valid_after_edit stage before after entry past sound
    (fun source member => (registered source member).reverse) input installed hit

end LeanPoo.Object.ClosAdmission.DispatchInvalidation
