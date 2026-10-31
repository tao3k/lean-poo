import LeanPoo.Prototype.GeneralizedClosure

/-! Narrow fixed points inside a wider raw carrier. Source guards and opaque
native exceptions remain operational controls, outside these pure equations. -/
namespace LeanPoo.Prototype.Generalized
universe u v w x
variable {Whole : Type u} {Raw : Type v} {Cooked : Type w} {Part : Type x}
/-- Close the actual viewed seed, then persistently replace just that component. -/
def closeFocused [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (put : Raw → Whole → Whole) (base : Raw) (whole : Whole) (budget : Nat) :
    Except String Whole := (closeWithin protocol parts base (get whole) budget).map
      (fun result => put result.closed.raw whole)
/-- With a lawful custom lens, successful replacement exposes the SAME local
fixed point; the claim does not imply a fixed point of arbitrary global equations. -/
theorem closeFocused_fixed [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (put : Raw → Whole → Whole) (laws : LensLaws get put)
    (base : Raw) (whole result : Whole) (budget : Nat)
    (accepted : closeFocused protocol parts get put base whole budget = .ok result) :
    protocol.step parts (get result) base = get result := by
  unfold closeFocused at accepted
  cases found : closeWithin protocol parts base (get whole) budget with
  | error message => simp [found, Except.map] at accepted
  | ok closed =>
    simp [found, Except.map] at accepted
    cases accepted
    rw [laws.put_get]
    exact closed.closed.fixed
/-- A successful wider result uses an actual local unfolding of its viewed input
seed, before budget exhaustion; it cannot substitute an unrelated fixed point. -/
theorem closeFocused_reached [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (put : Raw → Whole → Whole) (base : Raw) (whole result : Whole) (budget : Nat)
    (accepted : closeFocused protocol parts get put base whole budget = .ok result) :
    ∃ depth, depth < budget ∧ result = put (protocol.approximate parts base (get whole) depth) whole := by
  unfold closeFocused at accepted
  cases found : closeWithin protocol parts base (get whole) budget with
  | error message => simp [found, Except.map] at accepted
  | ok closed =>
    simp [found, Except.map] at accepted
    obtain ⟨depth,count,reached⟩ := closeWithin_reached protocol parts base (get whole) budget closed found
    have bound := closeWithin_bound protocol parts base (get whole) budget closed found
    rw [count] at bound
    exact ⟨depth,Nat.lt_of_lt_of_le (Nat.lt_succ_self depth) bound, by rw [reached]; exact accepted.symm⟩
/-- Preserving an independent audit/frame requires its own setter law. The three
lens laws alone do not specify which other observations must remain unchanged. -/
theorem closeFocused_frame [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (put : Raw → Whole → Whole) (frame : Whole → Frame)
    (preserves : ∀ raw source, frame (put raw source) = frame source)
    (base : Raw) (whole result : Whole) (budget : Nat)
    (accepted : closeFocused protocol parts get put base whole budget = .ok result) :
    frame result = frame whole := by
  unfold closeFocused at accepted
  cases found : closeWithin protocol parts base (get whole) budget with
  | error message => simp [found, Except.map] at accepted
  | ok closed =>
    simp [found, Except.map] at accepted
    cases accepted
    exact preserves _ _
/-- Final family admission checks the actual projected equation again. A later
overlapping update is accepted only if it preserves this equation. -/
def validateFocused [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (base : Raw) (whole : Whole) : Except String Unit :=
  if protocol.step parts (get whole) base = get whole then .ok ()
  else .error "later focused update invalidated an earlier raw closure"
/-- Successful final admission certifies the projected fixed-point equation. -/
theorem validateFocused_sound [DecidableEq Raw] (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (base : Raw) (whole : Whole)
    (accepted : validateFocused protocol parts get base whole = .ok ()) :
    protocol.step parts (get whole) base = get whole := by
  unfold validateFocused at accepted
  split at accepted
  · assumption
  · contradiction
/-- A later update through an independent focus preserves an earlier local
equation. This justifies composition, not arbitrary reordering of dependent stages. -/
theorem fixed_preserved {Other : Type} (protocol : Protocol Raw Cooked Part) (parts : List Part)
    (get : Whole → Raw) (putOther : Other → Whole → Whole)
    (preserves : ∀ source value, get (putOther value source) = get source)
    (base : Raw) (whole : Whole) (value : Other)
    (fixed : protocol.step parts (get whole) base = get whole) :
    protocol.step parts (get (putOther value whole)) base = get (putOther value whole) := by
  rw [preserves]
  exact fixed
end LeanPoo.Prototype.Generalized
