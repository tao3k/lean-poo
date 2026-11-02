import LeanPoo.Prototype.GeneralizedDeclaration
import LeanPoo.Prototype.LensLaws

/-! Controlled raw stabilization with a fixed step budget and actual equality.
No observational sampler or arbitrary comparison callback can certify a raw knot. -/
namespace LeanPoo.Prototype.Generalized
universe u v w
variable {Raw : Type u} {Cooked : Type v} {Part : Type w}
/-- Bounded closure retains the actual fixed equation and a raw transition count. -/
structure BoundedClosed (protocol : Protocol Raw Cooked Part) (parts : List Part) (base : Raw) where
  closed : Closed protocol parts base
  steps : Nat
/-- Every success comes from an adjacent raw equality. Budget failure is inconclusive
about divergence. The decidable equality is actual equality, not a user oracle. -/
def closeWithin [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) : Nat → Except String (BoundedClosed protocol parts base)
  | 0 => .error "closure budget exhausted"
  | budget + 1 =>
    let next := protocol.step parts seed base
    if stable : next = seed then .ok ⟨⟨seed,stable⟩,1⟩
    else (closeWithin protocol parts base next budget).map (fun result => {result with steps := result.steps + 1})
/-- The retained raw result satisfies the exact SAME fragment/base equation. -/
theorem closeWithin_fixed [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed protocol parts base)
    (_accepted : closeWithin protocol parts base seed budget = .ok result) :
    protocol.step parts result.closed.raw base = result.closed.raw := result.closed.fixed
/-- Successful search never spends more raw transitions than the supplied budget. -/
theorem closeWithin_bound [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed protocol parts base)
    (accepted : closeWithin protocol parts base seed budget = .ok result) : result.steps ≤ budget := by
  induction budget generalizing seed result with
  | zero => simp [closeWithin] at accepted
  | succ budget ih =>
    simp only [closeWithin] at accepted
    split at accepted
    · cases accepted; simp
    · cases found : closeWithin protocol parts base (protocol.step parts seed base) budget with
      | error message => simp [found, Except.map] at accepted
      | ok previous =>
        simp [found, Except.map] at accepted
        cases accepted
        have bound := ih _ _ found
        simpa using Nat.add_le_add_right bound 1
/-- Moving one real transition into the seed preserves finite unfolding semantics. -/
theorem Protocol.approximate_shift (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (depth : Nat) : protocol.approximate parts base seed (depth+1) =
      protocol.approximate parts base (protocol.step parts seed base) depth := by
  induction depth with
  | zero => rfl
  | succ more ih => exact congrArg (fun raw => protocol.step parts raw base) ih
/-- Conditional completeness: if the actual seed reaches a fixed point after d
advances, bounded search succeeds within d+1 calls, including equality verification.
No premise about eventual convergence is inferred from a finite budget. -/
theorem closeWithin_complete [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (depth : Nat)
    (stable : protocol.step parts (protocol.approximate parts base seed depth) base =
      protocol.approximate parts base seed depth) :
    ∃ result, closeWithin protocol parts base seed (depth+1) = .ok result := by
  induction depth generalizing seed with
  | zero =>
    exact ⟨⟨⟨seed,stable⟩,1⟩, by simp [closeWithin, show protocol.step parts seed base = seed from stable]⟩
  | succ depth ih =>
    by_cases current : protocol.step parts seed base = seed
    · exact ⟨⟨⟨seed,current⟩,1⟩, by simp [closeWithin,current]⟩
    · have shifted : protocol.step parts
          (protocol.approximate parts base (protocol.step parts seed base) depth) base =
          protocol.approximate parts base (protocol.step parts seed base) depth := by
        rw [← Protocol.approximate_shift]
        exact stable
      obtain ⟨result,found⟩ := ih _ shifted
      exact ⟨{result with steps := result.steps+1}, by
        rw [closeWithin]
        simp only [dite_eq_right current,found,Except.map]⟩
/-- A successful closure comes from the ORIGINAL seed's unfolding, not an arbitrary
other fixed point. The final transition counted by steps verifies adjacent equality. -/
theorem closeWithin_reached [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed protocol parts base)
    (accepted : closeWithin protocol parts base seed budget = .ok result) :
    ∃ depth, result.steps = depth+1 ∧ protocol.approximate parts base seed depth = result.closed.raw := by
  induction budget generalizing seed result with
  | zero => simp [closeWithin] at accepted
  | succ budget ih =>
    simp only [closeWithin] at accepted
    split at accepted
    · cases accepted; exact ⟨0,rfl,rfl⟩
    · cases found : closeWithin protocol parts base (protocol.step parts seed base) budget with
      | error message => simp [found, Except.map] at accepted
      | ok previous =>
        simp [found, Except.map] at accepted
        cases accepted
        obtain ⟨depth,count,reached⟩ := ih _ _ found
        exact ⟨depth+1, by simp [count], by rw [Protocol.approximate_shift]; exact reached⟩
/-- Every later unfolding of the ORIGINAL seed remains at the returned fixed point. -/
theorem closeWithin_forever [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed protocol parts base)
    (accepted : closeWithin protocol parts base seed budget = .ok result) (extra : Nat) :
    ∃ depth, result.steps = depth+1 ∧ protocol.approximate parts base seed (depth+extra) = result.closed.raw := by
  obtain ⟨depth,count,reached⟩ := closeWithin_reached protocol parts base seed budget result accepted
  have adjacent : protocol.approximate parts base seed depth = protocol.approximate parts base seed (depth+1) := by
    rw [Protocol.approximate_succ, reached, result.closed.fixed]
  exact ⟨depth,count,(protocol.stable parts base seed depth adjacent extra).trans reached⟩
/-- Once closed, all later finite observations keep the same raw result. -/
theorem BoundedClosed.stable (result : BoundedClosed protocol parts base) (extra : Nat) :
    protocol.approximate parts base result.closed.raw extra = result.closed.raw := by
  induction extra with
  | zero => rfl
  | succ more ih => rw [Protocol.approximate_succ, ih, result.closed.fixed]
/-- Atomic pure publication retains the old completed closure on refusal. -/
def publishClosed {ErrorType : Type} (old : α) (candidate : Except ErrorType α) : α :=
  match candidate with | .ok next => next | .error _ => old
/-- No exhausted prefix replaces the caller's published interface. -/
theorem publishClosed_refused {ErrorType : Type} (old : α) (failure : ErrorType) : publishClosed old (.error failure) = old := rfl
end LeanPoo.Prototype.Generalized
