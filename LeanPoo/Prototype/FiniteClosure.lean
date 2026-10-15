import LeanPoo.Prototype.FiniteFix

/-! Automatic least fixed points on explicitly finite-height ordered carriers.
Strict information growth supplies termination; no caller fuel or stability
witness is needed. Generalized-prototype future work. -/
namespace LeanPoo.Prototype.FiniteClosure

structure System (State : Type) where
  bottom : State
  below : State → State → Prop
  trans : ∀ {a b c}, below a b → below b c → below a c
  bottomBelow : ∀ state, below bottom state
  step : State → State
  monotone : ∀ {a b}, below a b → below (step a) (step b)
  height : Nat
  weight : State → Nat
  bounded : ∀ state, weight state ≤ height
  strict : ∀ {a b}, below a b → a ≠ b → weight a < weight b

variable {State : Type} [DecidableEq State] (system : System State)

def System.prototype : Proto State Unit State := fun self _ => system.step self

structure Closed where
  value : State
  fixed : system.step value = value
  least : ∀ other, system.step other = other → system.below value other
  depth : Nat
  bound : depth ≤ system.height
  reached : FiniteFix.iterate system.prototype () system.bottom depth = value

private def search (current : State) (depth : Nat)
    (reached : FiniteFix.iterate system.prototype () system.bottom depth = current)
    (rising : system.below current (system.step current))
    (lower : ∀ other, system.step other = other → system.below current other)
    (progress : depth ≤ system.weight current) : Closed system :=
  let next := system.step current
  if fixed : next = current then
    ⟨current,fixed,lower,depth,Nat.le_trans progress (system.bounded current),reached⟩
  else
    search (system.step current) (depth+1)
      (by change system.step (FiniteFix.iterate system.prototype () system.bottom depth) = _; rw [reached])
      (system.monotone rising)
      (by intro other stable; have below := system.monotone (lower other stable); simpa [stable] using below)
      (by have grows := system.strict rising (Ne.symm fixed); omega)
termination_by system.height - system.weight current
decreasing_by
  have grows := system.strict rising (Ne.symm fixed)
  have bounded := system.bounded (system.step current)
  omega

def close : Closed system :=
  search system system.bottom 0 rfl (system.bottomBelow _) (fun other _ => system.bottomBelow other) (Nat.zero_le _)

/-- Leastness selects the canonical solution even when a cyclic equation has
many fixed points. Any other least fixed point is equal under antisymmetry. -/
theorem least_unique (antisymm : ∀ {a b}, system.below a b → system.below b a → a = b)
    (other : State) (fixed : system.step other = other)
    (least : ∀ value, system.step value = value → system.below other value) :
    (close system).value = other :=
  antisymm ((close system).least other fixed) (least _ (close system).fixed)

/-- Automatic closure has the existing finite-unfolding semantics at every
later depth, rather than merely returning a locally checked equation. -/
theorem stable (extra : Nat) :
    FiniteFix.iterate system.prototype () system.bottom ((close system).depth+extra) = (close system).value := by
  rw [FiniteFix.stable_forever _ _ _ _ (by
    rw [(close system).reached]
    change (close system).value = system.step (FiniteFix.iterate system.prototype () system.bottom (close system).depth)
    rw [(close system).reached, (close system).fixed])]
  exact (close system).reached

end LeanPoo.Prototype.FiniteClosure
