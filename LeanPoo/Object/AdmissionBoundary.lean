-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.SourcePreparation
import Init.Data.List.Nat.Range
import Init.Data.List.Perm

/-! A necessary boundary for sparse method preparation.

An arbitrary finite adaptive audit cannot certify unknown siblings without
reading them. Constructor-owned recipes restrict the input domain instead;
that knowledge must come from construction and tracked storage, not a label.
This is an oracle-query lower bound, not a timer, an evaluator, or a claim
that every raw SlotSpec field is required by ordinary preparation. -/
namespace LeanPoo.Object.AdmissionBoundary

/-- A finite deterministic audit may choose later reads using earlier results.
The oracle stands for the producer's required admission facts. A true result
is acceptance. Author effects are separate intervals, not an oracle here. -/
inductive Audit where
  | done (accepted : Bool)
  | read (field : Nat) (next : Bool → Audit)

def run (facts : Nat → Bool) : Audit → Bool
  | .done accepted => accepted
  | .read field next => run facts (next (facts field))

def trace (facts : Nat → Bool) : Audit → List Nat
  | .done _ => []
  | .read field next => field :: trace facts (next (facts field))

/-- Adaptivity does not invalidate indistinguishability: agreeing on the
actual executed trace yields the same result AND the same next-read choices. -/
theorem trace_frame (audit : Audit) (before after : Nat → Bool)
    (same : ∀ field ∈ trace before audit, after field = before field) :
    run after audit = run before audit ∧ trace after audit = trace before audit := by
  induction audit with
  | done accepted => exact ⟨rfl, rfl⟩
  | read field next ih =>
    have head := same field (by simp [trace])
    have tail : ∀ query ∈ trace before (next (before field)), after query = before query :=
      fun query member => same query (List.mem_cons_of_mem _ member)
    simpa only [run, trace, head] using
      (ih (before field) tail).imp_right (congrArg (List.cons field))

def spoil (facts : Nat → Bool) (hidden : Nat) : Nat → Bool :=
  fun field => if field = hidden then false else facts field

theorem unread_spoil_invisible (audit : Audit) (facts : Nat → Bool) (hidden : Nat)
    (unread : hidden ∉ trace facts audit) :
    run (spoil facts hidden) audit = run facts audit ∧
      trace (spoil facts hidden) audit = trace facts audit := by
  apply trace_frame
  intro field member
  have other : field ≠ hidden := by
    intro same
    exact unread (same ▸ member)
  simp [spoil, other]

/-- Soundness is over ALL unknown sources. A compiler-owned source instead
has a smaller admissible domain and must justify that domain from its actual
constructors and writer/exposure coverage. -/
def Sound (required : Nat) (audit : Audit) : Prop :=
  ∀ facts, run facts audit = true → ∀ field < required, facts field = true

theorem accepted_unknown_reads_every_required (required : Nat) (audit : Audit)
    (sound : Sound required audit) (facts : Nat → Bool)
    (accepted : run facts audit = true) (field : Nat) (needed : field < required) :
    field ∈ trace facts audit := by
  by_cases visited : field ∈ trace facts audit
  · exact visited
  · have unchanged := (unread_spoil_invisible audit facts field visited).1
    have stillAccepted : run (spoil facts field) audit = true := unchanged.trans accepted
    have invalid := sound (spoil facts field) stillAccepted field needed
    simp [spoil] at invalid

/-- Repeated reads count too. Even a successful adaptive strategy performs at
least N oracle reads when N independent admission facts remain unknown. -/
theorem accepted_unknown_read_lower_bound (required : Nat) (audit : Audit)
    (sound : Sound required audit) (facts : Nat → Bool)
    (accepted : run facts audit = true) : required ≤ (trace facts audit).length := by
  have covered : List.range required ⊆ trace facts audit := by
    intro field member
    exact accepted_unknown_reads_every_required required audit sound facts accepted
      field (List.mem_range.mp member)
  simpa using (List.nodup_range.length_le_of_subset covered)

/-- The public finite-key functional constructor emits closure recipes. These
are installation-callable without running any body. A source-specific proof
can exploit this stronger input grammar; arbitrary raw specs cannot. -/
def generatedFacts {Self Value : Type}
    (recipes : Array (SourcePreparation.Recipe Self Value)) (field : Nat) : Bool :=
  match recipes[field]? with
  | none => true
  | some recipe => SlotPreparation.CapturedBinding.classified recipe.capture

theorem generated_facts_callable {Self Value : Type}
    (recipes : Array (SourcePreparation.Recipe Self Value)) (field : Nat) :
    generatedFacts recipes field = true := by
  unfold generatedFacts
  split
  · rfl
  · exact SourcePreparation.Recipe.callable _

/-- A no-read verdict is sound for the GENERATED domain, not all sources.
This proves only constructor classification. Payload capture, mutable metadata,
ordered refusal and entry/return authentication remain separate obligations. -/
theorem generated_classification_needs_no_probe {Self Value : Type}
    (recipes : Array (SourcePreparation.Recipe Self Value)) :
    run (generatedFacts recipes) (.done true) = true ∧
      trace (generatedFacts recipes) (.done true) = [] ∧
      ∀ field < recipes.size, generatedFacts recipes field = true := by
  exact ⟨rfl, rfl, fun field _ => generated_facts_callable recipes field⟩

theorem no_probe_is_not_universal_admission : ¬ Sound 1 (.done true) := by
  intro sound
  have impossible := sound (fun _ => false) rfl 0 (by decide)
  cases impossible

end LeanPoo.Object.AdmissionBoundary
