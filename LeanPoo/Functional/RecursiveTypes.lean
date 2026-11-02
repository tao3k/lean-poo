import LeanPoo.Prototype.Recursive

/-! Explicit finite Mu approximants, advancing the type-system future work.
F is a capture-avoiding guarded body substitution in Scheme. These laws do not
identify a finite approximation with an unrestricted equirecursive fixed point. -/
namespace LeanPoo.Functional.RecursiveTypes
open LeanPoo.Prototype.Recursive

/-- Repeated guarded body substitution starts from an explicitly empty base. -/
def unfold (body : α → α) (bottom : α) : Nat → α
  | 0 => bottom
  | n + 1 => body (unfold body bottom n)

/-- The program reuses explicit final-self requests, never an eager host knot. -/
def program (body : α → α) (bottom : α) : Generator Nat α
  | 0 => .value bottom
  | n + 1 => .call n (fun prior => .value (body prior))

/-- Exact correspondence between finite expansion and existing safe recursion. -/
theorem closes (body : α → α) (bottom : α) (depth : Nat) :
    solve (program body bottom) (depth + 1) depth = .value (unfold body bottom depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [solve]
    change Interaction.interpret (solve (program body bottom) (depth + 1))
      (.call depth (fun prior => .value (body prior))) = _
    rw [Interaction.interpret, ih]
    rfl


/-- A finite expansion needs at most one previous-depth request per unfolding.
Branching body copies are separately charged by the Scheme work counter. -/
theorem unfold_step (body : α → α) (bottom : α) (depth : Nat) :
    unfold body bottom (depth + 1) = body (unfold body bottom depth) := rfl

/-- A metadata transformation commutes with every finite approximant when it
preserves bottom and the admitted body substitution. These explicit premises
exclude binder capture; no unbounded fixed point or callback law is inferred. -/
theorem unfold_transform (transform : α → β) (source : α → α) (target : β → β)
    (bottom : α) (initial : β) (base : transform bottom = initial)
    (step : ∀ value, transform (source value) = target (transform value)) (depth : Nat) :
    transform (unfold source bottom depth) = unfold target initial depth := by
  induction depth with
  | zero => exact base
  | succ depth ih => simp only [unfold, step, ih]

/-- Guardedness in Scheme is syntactic; this semantic monotonicity premise states
what increasing a recursive approximation means for observational replacement. -/
theorem increasing (relation : α → α → Prop) (body : α → α) (bottom : α)
    (least : ∀ value, relation bottom value)
    (monotone : ∀ a b, relation a b → relation (body a) (body b)) (depth : Nat) :
    relation (unfold body bottom depth) (unfold body bottom (depth + 1)) := by
  induction depth with
  | zero => exact least _
  | succ depth ih => exact monotone _ _ ih

/-- The bounded admission protocol distinguishes incomplete expansion from an
ordinary value outside the completed finite approximation. No partial success. -/
def bounded (needed budget : Nat) (body : α → α) (bottom : α) (depth : Nat) : Except Unit α :=
  if needed ≤ budget then .ok (unfold body bottom depth) else .error ()

/-- Budget exhaustion does not admit any already-computed expansion prefix. -/
theorem exhausted (needed budget : Nat) (body : α → α) (bottom : α) (depth : Nat)
    (short : budget < needed) : bounded needed budget body bottom depth = .error () := by
  simp [bounded, Nat.not_le.mpr short]

/-- Completed bounded expansion returns precisely the declared approximation. -/
theorem completed (needed budget : Nat) (body : α → α) (bottom : α) (depth : Nat)
    (result : bounded needed budget body bottom depth = .ok value) : value = unfold body bottom depth := by
  unfold bounded at result
  split at result
  · exact (Except.ok.inj result).symm
  · contradiction
end LeanPoo.Functional.RecursiveTypes
