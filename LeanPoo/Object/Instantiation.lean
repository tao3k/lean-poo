/-! Explicit admission, optional construction hooks, lookup and active-slot guards.
These pure boundaries do not model native callback effects or thread scheduling. -/
namespace LeanPoo.Object
/-- Explicit checked construction: pure class admission, optional user hook,
and fresh admission of its result. Native callback effects are not rolled back. -/
def instantiateChecked (valid : Value → Bool) (hook : Option (Value → Except String Value))
    (candidate : Value) : Except String Value :=
  if valid candidate then
    match hook with
    | none => .ok candidate
    | some run => do
      let result ← run candidate
      if valid result then .ok result else .error "invalid instance"
  else .error "invalid instance"
/-- Rejected input never invokes the construction hook. -/
theorem instantiateChecked_rejected (valid : Value → Bool)
    (hook : Option (Value → Except String Value)) (candidate : Value) (bad : valid candidate = false) :
    instantiateChecked valid hook candidate = .error "invalid instance" := by
  simp [instantiateChecked, bad]
/-- Every successfully returned value meets current admission, including replacements. -/
theorem instantiateChecked_valid (valid : Value → Bool)
    (hook : Option (Value → Except String Value)) (candidate result : Value)
    (accepted : instantiateChecked valid hook candidate = .ok result) : valid result = true := by
  cases input : valid candidate with
  | false => simp [instantiateChecked, input] at accepted
  | true =>
    cases hook with
    | none =>
      have same : candidate = result := by simpa [instantiateChecked, input] using accepted
      simpa [← same] using input
    | some run =>
      cases performed : run candidate with
      | error message => simp [instantiateChecked, input, performed, bind, Except.bind] at accepted
      | ok next =>
        cases checked : valid next <;> simp [instantiateChecked, input, performed, checked, bind, Except.bind] at accepted
        subst result
        exact checked
/-- Optional lookup distinguishes a stored false-like value from an absent slot.
The fallback thunk is selected only for absence; native sharing is tested separately. -/
def fallbackTo (direct : Key → Option Value) (fallback : Unit → Key → Option Value) (key : Key) :
    Option Value := match direct key with | some value => some value | none => fallback () key
/-- A direct slot bypasses fallback, irrespective of its implementation. -/
theorem fallbackTo_present (direct : Key → Option Value) (fallback : Unit → Key → Option Value)
    (key : Key) (value : Value) (present : direct key = some value) :
    fallbackTo direct fallback key = some value := by simp [fallbackTo, present]
/-- Missing lookup uses the delegate's ordinary result, including absence. -/
theorem fallbackTo_missing (direct : Key → Option Value) (fallback : Unit → Key → Option Value)
    (key : Key) (missing : direct key = none) : fallbackTo direct fallback key = fallback () key := by
  simp [fallbackTo, missing]
/-- Guard one receiver/key computation. The native dynamic scope unwinds on
exceptions; this pure model states the guard and successor-path equations. -/
def guardSlot [DecidableEq Key] (active : List Key) (key : Key)
    (compute : List Key → Except String Value) : Except String Value :=
  if key ∈ active then .error "cyclic slot" else compute (key :: active)
/-- Repeating an active receiver/key fails without invoking the source again. -/
theorem guardSlot_cycle [DecidableEq Key] (active : List Key) (key : Key)
    (compute : List Key → Except String Value) (repeated : key ∈ active) :
    guardSlot active key compute = .error "cyclic slot" := by simp [guardSlot, repeated]
/-- An independent key sees the new active frame, preserving source errors. -/
theorem guardSlot_fresh [DecidableEq Key] (active : List Key) (key : Key)
    (compute : List Key → Except String Value) (fresh : key ∉ active) :
    guardSlot active key compute = compute (key :: active) := by simp [guardSlot, fresh]
/-- Private guard pairs are heap cells; their payloads identify receiver/slot keys.
Public diagnostic copies need separate cell identities, not just an outer list. -/
def guardKeys (heap : Nat → Key) (cells : List Nat) : List Key := cells.map heap

/-- Editing only disjoint diagnostic cells preserves the whole private guard.
Fresh pair allocation and the write footprint are standard-host premises. -/
theorem guardKeys_diagnostic_frame (before after : Nat → Key) (active exposed : List Nat)
    (separate : ∀ id, id ∈ active → id ∉ exposed)
    (writes : ∀ id, id ∉ exposed → after id = before id) :
    guardKeys after active = guardKeys before active := by
  apply List.map_congr_left
  intro id present
  exact writes id (separate id present)

/-- Caller edits of owned diagnostics cannot change cycle-versus-fresh dispatch. -/
theorem guardSlot_diagnostic_frame [DecidableEq Key] (before after : Nat → Key)
    (active exposed : List Nat) (key : Key) (compute : List Key → Except String Value)
    (separate : ∀ id, id ∈ active → id ∉ exposed)
    (writes : ∀ id, id ∉ exposed → after id = before id) :
    guardSlot (guardKeys after active) key compute =
      guardSlot (guardKeys before active) key compute := by
  rw [guardKeys_diagnostic_frame before after active exposed separate writes]

/-- A still-active key refuses without invoking its body after diagnostic edits. -/
theorem guardSlot_diagnostic_cycle [DecidableEq Key] (before after : Nat → Key)
    (active exposed : List Nat) (key : Key) (compute : List Key → Except String Value)
    (separate : ∀ id, id ∈ active → id ∉ exposed)
    (writes : ∀ id, id ∉ exposed → after id = before id)
    (repeated : key ∈ guardKeys before active) :
    guardSlot (guardKeys after active) key compute = .error "cyclic slot" := by
  rw [guardSlot_diagnostic_frame before after active exposed key compute separate writes]
  exact guardSlot_cycle _ _ _ repeated

/-- Error-only snapshot construction retains chronological key order. -/
def cycleDiagnostic (active : List Key) (key : Key) : List Key := (key :: active).reverse

/-- Receiver/slot payload identities and occurrence order survive the snapshot. -/
theorem cycleDiagnostic_order (active : List Key) (key : Key) :
    cycleDiagnostic active key = active.reverse ++ [key] := by
  simp [cycleDiagnostic]

/-- Count diagnostic spine and pair cells only; guard comparisons, the new key,
callbacks, exception objects, allocation/GC and wall time are separate costs. -/
def cycleDiagnosticCells (cyclic : Bool) (depth : Nat) : Nat :=
  if cyclic then (depth + 1) + (depth + 1) else 0

/-- Successful demand introduces no diagnostic copying work. -/
theorem cycleDiagnosticCells_hot (depth : Nat) : cycleDiagnosticCells false depth = 0 := rfl

/-- A cycle pays one outer cell and one independent pair per reported entry. -/
theorem cycleDiagnosticCells_error (depth : Nat) :
    cycleDiagnosticCells true depth = (depth + 1) + (depth + 1) := rfl

end LeanPoo.Object
