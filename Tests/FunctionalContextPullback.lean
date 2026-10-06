import LeanPoo.Functional.ContextPullback

namespace LeanPoo.Tests.FunctionalContextPullback
open Functional Requirements
private inductive Key where
  | quantity | limit | enabled
  deriving BEq, DecidableEq, Repr
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .limit => Nat
  | .enabled => Bool
private def source : (key : Key) → Factory Nat (fun c => Value c key)
  | .quantity => fun c => ⟨c+1, by omega⟩
  | .limit => fun c => c+2
  | .enabled => fun _ => true
private def available (mask : Nat) : Key → Bool
  | .quantity => mask % 2 == 1
  | .limit => mask / 2 % 2 == 1
  | .enabled => mask / 4 % 2 == 1
private def provider (mask : Nat) : Provider Nat Key Value :=
  fun key => if available mask key then some (source key) else none
private def expected (c : Nat) : (keys : List Key) → Results Value c keys
  | [] => PUnit.unit
  | key :: rest => (source key c, expected c rest)
private theorem selected_expected (mask : Nat) (keys : List Key)
    (factories : Factories Nat Value keys) (selected : Selected (provider mask) keys factories) :
    ∀ c, build factories c = expected c keys := by
  induction keys with
  | nil => cases factories; intro c; rfl
  | cons key rest ih =>
    rcases factories with ⟨head, tail⟩
    have chosen := selected.1
    have enabled : available mask key = true := by
      cases found : available mask key <;> simp [provider, found] at chosen ⊢
    have same : source key = head := by simpa [provider, enabled] using chosen
    intro c
    simp only [build, expected, same, ih tail selected.2 c]
    rfl

private def requests (mask : Nat) : List Key :=
  [Key.quantity, .limit, .enabled].filter (available mask)
private def score (c : Nat) : (keys : List Key) → Results Value c keys → Nat
  | [], _ => 0
  | .quantity :: rest, (head, tail) => head.val + score c rest tail
  | .limit :: rest, (head, tail) => Nat.add head (score c rest tail)
  | .enabled :: rest, (head, tail) => (cond head 1 0) + score c rest tail
private def scalar (c : Nat) (keys : List Key) : Nat :=
  (keys.map fun key => match key with
    | .quantity => c+1
    | .limit => c+2
    | .enabled => 1).sum

/-- Extra context includes a function, with no executable equality supplied. -/
private structure Outer where
  base : Nat
  tag : Nat
  callback : Nat → Nat
private def project (outer : Outer) := outer.base
private def trace : List Outer :=
  [0,0,7,7,0,23,23,23,0].zipIdx.map fun (base, tag) =>
    ⟨base, tag, fun n => n + tag⟩
private def check (mask : Nat) (keys : List Key) : IO (Nat × Nat) := do
  let Claim := fun c data => data = expected c keys
  match prepareCertified (provider mask) keys Claim (selected_expected mask keys) with
  | .error actual =>
    unless some actual == keys.find? (fun key => !(available mask key)) do
      throw (IO.userError "pullback first error")
    return (0,0)
  | .ok ready =>
    let construct := fun outer data (_ : Claim (project outer) data) =>
      (⟨score (project outer) keys data + outer.tag + outer.callback outer.tag,
        by omega⟩ : {n : Nat // outer.tag ≤ n})
    let mut slot := ContextSlot.empty ready
    let mut previous : Option Nat := none
    let mut reads := 0
    let mut hits := 0
    for outer in trace do
      let (output, next, hit) := slot.consumeAlong project construct outer
      let uncached := construct outer (build ready.factories (project outer)) (ready.valid _)
      unless output.val == scalar outer.base keys + outer.tag + (outer.tag + outer.tag) &&
          output.val == uncached.val do throw (IO.userError "outer constructor/independent mismatch")
      unless hit == (previous == some outer.base) do throw (IO.userError "projected hit mismatch")
      match next.retained with
      | none => throw (IO.userError "missing base snapshot")
      | some ⟨saved, _⟩ => unless saved == outer.base do throw (IO.userError "wrong base context")
      slot := next
      previous := some outer.base
      reads := reads+1
      if hit then hits := hits+1
    return (reads,hits)
#eval do
  let mut cases := 0
  let mut reads := 0
  let mut hits := 0
  for mask in List.range 8 do
    for requested in List.range 8 do
      let keys := requests requested
      for keys in [keys, keys.reverse, keys ++ keys] do
        let (count, reused) ← check mask keys
        reads := reads+count
        hits := hits+reused
        cases := cases+1
  unless cases == 192 && reads == 729 && hits == 324 do
    throw (IO.userError "pullback coverage")
  IO.println s!"FUNCTIONAL-CONTEXT-PULLBACK-OK cases={cases} reads={reads} hits={hits} misses={reads-hits} outer_eq=not-required"

/- An arbitrary varying outer-dependent value is outside the fixed base family. -/
example : True := by
  fail_if_success have _outerEq : DecidableEq Outer := inferInstance
  trivial
example (ready : Certified (Value := Value) [Key.quantity] (fun _ _ => True))
    (slot : ContextSlot ready) (outer : Outer) :
    outer.base ≤ ((slot.readAlong project outer).1.val).1.val :=
  ((slot.readAlong project outer).1.val).1.property
example (ready : Certified (Value := Value) [Key.quantity] (fun _ _ => True))
    (_slot : ContextSlot ready) (_outer : Outer) : True := by
  fail_if_success have _wrong : Snapshot ready (_outer.base+1) := (_slot.readAlong project _outer).1
  trivial
/- Dropping a genuinely varying dependency cannot justify a base cache. -/
example : ¬ ∃ f : Nat → Nat, ∀ outer : Outer, f (project outer) = outer.base + outer.tag := by
  rintro ⟨f, factored⟩
  have first := factored ⟨0, 0, fun _ => 0⟩
  have second := factored ⟨0, 1, fun _ => 0⟩
  change f 0 = 0 + 0 at first
  change f 0 = 0 + 1 at second
  omega
#print axioms ContextSlot.readAlong_value
#print axioms ContextSlot.readAlong_hit
#print axioms ContextSlot.consumeAlong_value
#print axioms ContextSlot.consumeAlong_reindex
