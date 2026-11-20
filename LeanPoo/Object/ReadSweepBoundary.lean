import LeanPoo.Object.ReadRouteRuns

namespace LeanPoo.Object.ReadRouteRuns.Sizing

/-- Gerbil HashTable.length is an interface call. Its callback can change the
window after issuance preflight, even when the outer action is exact void. -/
def reference (before : Window) (reads : List Read)
    (size : Window → Except Refusal (Window × Nat)) : Except Refusal Unit := do
  preflight before reads
  let (after, _) ← size before
  serial after reads

def guarded (before : Window) (reads : List Read)
    (native : Bool) (size : Window → Except Refusal (Window × Nat)) : Except Refusal Unit := do
  preflight before reads
  let (after, _) ← size before
  serial (if native then preissued after else after) reads

/-- Eligibility must derive from the live length delegate before invoking it.
Only native sizing can retain the preflight. The fallback authenticates every
row after the callback, in the original issue/key/route/live order. -/
theorem guarded_exact (before : Window) (reads : List Read)
    (native : Bool) (size : Window → Except Refusal (Window × Nat))
    (preserves : native = true → ∀ after count,
      size before = .ok (after, count) → ∀ read ∈ reads,
      after.issue read = before.issue read) :
    guarded before reads native size = reference before reads size := by
  unfold guarded reference
  cases admitted : preflight before reads with
  | error cause => rfl
  | ok value =>
    cases value
    simp only [Bind.bind, Except.bind]
    cases sized : size before with
    | error cause => rfl
    | ok pair =>
      rcases pair with ⟨after, count⟩
      cases flag : native with
      | false => rfl
      | true =>
        simp only [ite_true]
        apply serial_preissued_eq
        intro read member
        rw [preserves flag after count sized read member]
        exact (preflight_ok_iff before reads).mp admitted read member

private def good : Window where
  issue _ := .ok ()
  key _ := .ok ()
  route _ := .ok ()
  live _ := .ok ()

private def changed : Window := { good with issue := fun _ => .error .issuance }
private def lengthCallback (_ : Window) : Except Refusal (Window × Nat) := .ok (changed, 1)

/-- Treating interface sizing as pure accepts a changed record. No method
body or ordinary observer is required for the counterexample. -/
example : guarded good [⟨0, false, 0⟩] true lengthCallback = .ok () ∧
    reference good [⟨0, false, 0⟩] lengthCallback = .error .issuance := by
  constructor <;> rfl

example : guarded good [⟨0, false, 0⟩] false lengthCallback = .error .issuance := rfl

end LeanPoo.Object.ReadRouteRuns.Sizing
