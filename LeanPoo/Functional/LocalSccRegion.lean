-- SPDX-FileCopyrightText: 2026 tao3k team and Contributors
-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.StrongComponents

/- Local SCC replacement over a certified union of old and new edges.
   This proves relational equivalence, not the runtime work bound or Tarjan
   implementation. Both remain independent Scheme obligations. -/
namespace LeanPoo.Functional.LocalSccRegion
open LeanPoo.Functional.StrongComponents

abbrev Edge (n : Nat) := Fin n → Fin n → Bool

def Region {n : Nat} (union : Edge n) (root : Fin n → Prop) (node : Fin n) : Prop :=
  (∃ seed, root seed ∧ Reach union seed node) ∧
  (∃ seed, root seed ∧ Reach union node seed)

def Same {n : Nat} (edge : Edge n) (a b : Fin n) : Prop :=
  Reach edge a b ∧ Reach edge b a

theorem lift_path {n : Nat} {source target : Edge n}
    (embedded : ∀ a b, source a b = true → target a b = true)
    {a b : Fin n} (path : Reach source a b) : Reach target a b := by
  induction path with
  | refl a => exact .refl a
  | step direct _ ih => exact .step (embedded _ _ direct) ih

theorem outside_cycle_has_no_root {n : Nat} {union : Edge n} {root : Fin n → Prop}
    {anchor node : Fin n} (outside : ¬ Region union root anchor)
    (outward : Reach union anchor node) (homeward : Reach union node anchor) :
    ¬ root node := by
  intro edited
  exact outside ⟨⟨node, edited, homeward⟩, ⟨node, edited, outward⟩⟩

theorem transport_segment {n : Nat} {source target union : Edge n} {root : Fin n → Prop}
    (embedded : ∀ a b, source a b = true → union a b = true)
    (sameRows : ∀ a, ¬ root a → ∀ b, source a b = target a b)
    {anchor start finish : Fin n} (outside : ¬ Region union root anchor)
    (path : Reach source start finish) :
    Reach union anchor start → Reach union finish anchor → Reach target start finish := by
  induction path with
  | refl a => intro _ _; exact .refl a
  | @step a b c direct tail ih =>
    intro pathIn pathOut
    have toAnchor : Reach union a anchor :=
      (Reach.step (embedded a b direct) (lift_path embedded tail)).trans pathOut
    have clean := outside_cycle_has_no_root outside pathIn toAnchor
    have nextPrefix : Reach union anchor b :=
      pathIn.trans (.step (embedded a b direct) (.refl b))
    exact .step ((sameRows a clean b) ▸ direct) (ih nextPrefix pathOut)

theorem outside_components_preserved {n : Nat} {old next union : Edge n}
    {root : Fin n → Prop}
    (oldEmbedded : ∀ a b, old a b = true → union a b = true)
    (newEmbedded : ∀ a b, next a b = true → union a b = true)
    (sameRows : ∀ a, ¬ root a → ∀ b, old a b = next a b)
    {a b : Fin n} (outside : ¬ Region union root a) :
    Same old a b ↔ Same next a b := by
  constructor
  · rintro ⟨there, back⟩
    exact ⟨transport_segment oldEmbedded sameRows outside there (.refl a)
        (lift_path oldEmbedded back),
      transport_segment oldEmbedded sameRows outside back
        (lift_path oldEmbedded there) (.refl a)⟩
  · rintro ⟨there, back⟩
    have symmetric : ∀ a, ¬ root a → ∀ b, next a b = old a b :=
      fun a clean b => (sameRows a clean b).symm
    exact ⟨transport_segment newEmbedded symmetric outside there (.refl a)
        (lift_path newEmbedded back),
      transport_segment newEmbedded symmetric outside back
        (lift_path newEmbedded there) (.refl a)⟩

theorem between_region_endpoints {n : Nat} {union : Edge n} {root : Fin n → Prop}
    {a middle b : Fin n} (left : Region union root a) (right : Region union root b)
    (pathIn : Reach union a middle) (pathOut : Reach union middle b) :
    Region union root middle := by
  obtain ⟨seed, edited, path⟩ := left.1
  obtain ⟨exit, changed, tail⟩ := right.2
  exact ⟨⟨seed, edited, path.trans pathIn⟩, ⟨exit, changed, pathOut.trans tail⟩⟩

theorem region_contains_component {n : Nat} {edge union : Edge n} {root : Fin n → Prop}
    (embedded : ∀ a b, edge a b = true → union a b = true)
    {a b : Fin n} (inside : Region union root a) (same : Same edge a b) :
    Region union root b :=
  between_region_endpoints inside inside (lift_path embedded same.1) (lift_path embedded same.2)

noncomputable def restricted {n : Nat} (edge union : Edge n) (root : Fin n → Prop) : Edge n :=
  fun a b => @ite Bool (Region union root a ∧ Region union root b)
    (Classical.propDecidable _) (edge a b) false

theorem restricted_embeds {n : Nat} {edge union : Edge n} {root : Fin n → Prop}
    {a b : Fin n} (direct : restricted edge union root a b = true) : edge a b = true := by
  classical
  unfold restricted at direct
  split at direct
  · exact direct
  · contradiction

theorem restrict_path {n : Nat} {edge union : Edge n} {root : Fin n → Prop}
    (embedded : ∀ a b, edge a b = true → union a b = true)
    {a b : Fin n} (path : Reach edge a b) :
    Region union root a → Region union root b → Reach (restricted edge union root) a b := by
  classical
  induction path with
  | refl a => intro _ _; exact .refl a
  | @step a b c direct tail ih =>
    intro left right
    have middle := between_region_endpoints left right
      (Reach.step (embedded a b direct) (.refl b)) (lift_path embedded tail)
    exact .step (by simp [restricted, left, middle, direct]) (ih middle right)

theorem inside_components_exact {n : Nat} {edge union : Edge n} {root : Fin n → Prop}
    (embedded : ∀ a b, edge a b = true → union a b = true)
    {a b : Fin n} (inside : Region union root a) :
    Same edge a b ↔ Same (restricted edge union root) a b := by
  constructor
  · intro same
    have other := region_contains_component embedded inside same
    exact ⟨restrict_path embedded same.1 inside other,
      restrict_path embedded same.2 other inside⟩
  · rintro ⟨there, back⟩
    exact ⟨lift_path (fun _ _ direct => restricted_embeds direct) there,
      lift_path (fun _ _ direct => restricted_embeds direct) back⟩

/-- Replacing only local SCCs and retaining old outside membership is exact.
    The union can be old edges plus admitted additions; deleted old edges
    remain in the envelope. Thus deletion, replacement and merging share
    this law without claiming all changes are insertion-only. -/
theorem local_replacement_equals_cold {n : Nat} {old next union : Edge n}
    {root : Fin n → Prop}
    (oldEmbedded : ∀ a b, old a b = true → union a b = true)
    (newEmbedded : ∀ a b, next a b = true → union a b = true)
    (sameRows : ∀ a, ¬ root a → ∀ b, old a b = next a b)
    (a b : Fin n) :
    Same next a b ↔
      @ite Prop (Region union root a) (Classical.propDecidable _)
        (Same (restricted next union root) a b) (Same old a b) := by
  classical
  by_cases inside : Region union root a
  · simp only [ite_eq_left inside]
    exact inside_components_exact newEmbedded inside
  · simp only [ite_eq_right inside]
    exact (outside_components_preserved oldEmbedded newEmbedded sameRows inside).symm

-- Matched finite control: retaining deleted old edges in the envelope matters.
-- If only the new graph were used, owner 1 would look outside the region,
-- although its old component with owner 0 must split after deleting 0 -> 1.
private def cycleTwo : Edge 2 := fun a b => a != b
private def cutTwo : Edge 2 := fun a b => a == 1 && b == 0
private def finiteRegion (edge : Edge 2) (node : Fin 2) : Bool :=
  reachable edge 2 0 node && reachable edge 2 node 0

#guard finiteRegion cycleTwo 1
#guard !finiteRegion cutTwo 1
#guard reachable cycleTwo 2 0 1 && reachable cycleTwo 2 1 0
#guard !(reachable cutTwo 2 0 1 && reachable cutTwo 2 1 0)

end LeanPoo.Functional.LocalSccRegion
