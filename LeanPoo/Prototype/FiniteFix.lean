import LeanPoo.Prototype.CheckedFunction

/-! Pure finite unfoldings of the paper's `fix` nucleus. They give a total,
inspectable semantics for a chosen depth. Stabilization is an explicit proof
premise; unrestricted recursive instantiation remains a separate operation. -/

namespace LeanPoo.Prototype
namespace FiniteFix

/-- Unfold an open-recursive prototype a finite number of times from a seed. -/
def iterate (prototype : Proto α β α) (base : β) (seed : α) : Nat → α
  | 0 => seed
  | depth + 1 => prototype (iterate prototype base seed depth) base

theorem unfold (prototype : Proto α β α) (base : β) (seed : α) (depth : Nat) :
    iterate prototype base seed (depth + 1) =
      prototype (iterate prototype base seed depth) base := rfl

/-- One `mix` step passes the same finite self approximation through both
parent and child, in the paper's child-over-parent order. -/
theorem unfold_compose (child : Proto α Middle α)
    (parent : Proto α β Middle) (base : β) (seed : α) (depth : Nat) :
    iterate (compose child parent) base seed (depth + 1) =
      child (iterate (compose child parent) base seed depth)
        (parent (iterate (compose child parent) base seed depth) base) := rfl

/-- An equal adjacent pair is an actual fixed point of the prototype. -/
def certified (prototype : Proto α β α) (base : β) (seed : α) (depth : Nat)
    (stable : iterate prototype base seed depth =
      iterate prototype base seed (depth + 1)) :
    { value : α // prototype value base = value } :=
  ⟨iterate prototype base seed depth, by simpa only [unfold] using stable.symm⟩

/-- Once an unfolding stabilizes, no later finite unfolding changes it. -/
theorem stable_forever (prototype : Proto α β α) (base : β) (seed : α)
    (depth : Nat)
    (stable : iterate prototype base seed depth =
      iterate prototype base seed (depth + 1)) (extra : Nat) :
    iterate prototype base seed (depth + extra) =
      iterate prototype base seed depth := by
  have fixed : prototype (iterate prototype base seed depth) base =
      iterate prototype base seed depth := by
    simpa only [unfold] using stable.symm
  induction extra with
  | zero => simp
  | succ more ih =>
    rw [Nat.add_succ, unfold, ih]
    exact fixed

end FiniteFix

/-- A total observation of a checked recursive function with a fuel bound. -/
def CheckedFunction.approximate
    (prototype : Proto (CheckedFunction Input Output)
      (CheckedFunction Input Output) (CheckedFunction Input Output))
    (depth : Nat) : CheckedFunction Input Output :=
  FiniteFix.iterate prototype CheckedFunction.bottom CheckedFunction.bottom depth

theorem CheckedFunction.approximate_zero
    (prototype : Proto (CheckedFunction Input Output)
      (CheckedFunction Input Output) (CheckedFunction Input Output)) :
    CheckedFunction.approximate prototype 0 = CheckedFunction.bottom := rfl

theorem CheckedFunction.approximate_succ
    (prototype : Proto (CheckedFunction Input Output)
      (CheckedFunction Input Output) (CheckedFunction Input Output))
    (depth : Nat) :
    CheckedFunction.approximate prototype (depth + 1) =
      prototype (CheckedFunction.approximate prototype depth)
        CheckedFunction.bottom := rfl

end LeanPoo.Prototype
