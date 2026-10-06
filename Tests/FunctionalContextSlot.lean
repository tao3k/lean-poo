import LeanPoo.Functional.ContextSlot
import LeanPoo.Functional.ResultView

namespace LeanPoo.Tests.FunctionalContextSlot
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

private def jointKeys : List Key := [.quantity, .limit, .enabled, .quantity]
private def Joint (c : Nat) (data : Results Value c jointKeys) : Prop :=
  data.1.val ≤ data.2.1 ∧ data.2.2.1 = true ∧ data.2.2.2.1 = data.1
private theorem joint_admit (mask : Nat) (factories : Factories Nat Value jointKeys)
    (selected : Selected (provider mask) jointKeys factories) :
    ∀ c, Joint c (build factories c) := by
  intro c
  rw [selected_expected mask jointKeys factories selected c]
  simp [Joint, expected, jointKeys, source]
  constructor <;> rfl


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

private def traces : List (List Nat) := [[0,0,7,7,0,23,23], [0,7,0,7,0], [23,23,23], []]
private def check (mask : Nat) (keys : List Key) : IO (Nat × Nat) := do
  let Claim := fun c data => data = expected c keys
  match prepareCertified (provider mask) keys Claim (selected_expected mask keys) with
  | .error key =>
    unless some key == keys.find? (fun key => !(available mask key)) do
      throw (IO.userError "slot preparation first error")
    return (0,0)
  | .ok ready =>
    let construct := fun c data (_ : Claim c data) => score c keys data
    let mut reads := 0
    let mut hits := 0
    for trace in traces do
      let mut slot := ContextSlot.empty ready
      let mut previous : Option Nat := none
      for c in trace do
        let (output, next, reused) := slot.consume construct c
        unless output == scalar c keys && output == ready.consume construct c do
          throw (IO.userError "cached/uncached/scalar mismatch")
        unless reused == (previous == some c) do throw (IO.userError "reuse decision mismatch")
        match next.retained with
        | none => throw (IO.userError "missing replacement pair")
        | some ⟨saved, _⟩ => unless saved == c do throw (IO.userError "wrong retained context")
        slot := next
        previous := some c
        reads := reads+1
        if reused then hits := hits+1
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
  unless reads == 1215 && hits == 405 do throw (IO.userError "trace coverage mismatch")
  IO.println s!"FUNCTIONAL-CONTEXT-SLOT-OK cases={cases} reads={reads} hits={hits} misses={reads-hits} traces=4"

#eval do
  match prepareCertified (provider 7) jointKeys Joint (joint_admit 7) with
  | .error _ => throw (IO.userError "joint family unavailable")
  | .ok ready =>
    let construct := fun c data (_ : Joint c data) => Nat.add data.1.val data.2.1
    let (_, slot, first) := (ContextSlot.empty ready).consume construct 0
    let twin : Certified jointKeys Joint := ⟨ready.factories, fun c => ready.valid c⟩
    let (result, same, reused) := (slot.rebind twin rfl).consume construct 0
    let (_, changed, miss) := same.consume construct 7
    let (_, _, evicted) := changed.consume construct 0
    unless result == 3 && !first && reused && !miss && !evicted do
      throw (IO.userError "rebind/context replacement mismatch")
    IO.println "FUNCTIONAL-CONTEXT-SLOT-REBIND-OK hit=1 replaced=2"

/- Independent context indices are not interchangeable cached data. -/
example (ready : Certified jointKeys Joint) (_snapshot : Snapshot ready 0) : True := by
  fail_if_success have _wrong : Snapshot ready 9 := _snapshot
  trivial
/- Equal joint predicates are insufficient to reuse a changed factory family. -/
example (left _right : Certified jointKeys Joint) (_slot : ContextSlot left) : True := by
  fail_if_success have _wrong : ContextSlot _right := _slot
  trivial
example (ready : Certified jointKeys Joint) (slot : ContextSlot ready) (c : Nat) :
    (slot.read c).1.val = build ready.factories c := slot.read_value c
#print axioms ContextSlot.read_hit
#print axioms ContextSlot.read_miss
#print axioms ContextSlot.read_value
#print axioms ContextSlot.consume_value

#print axioms ContextSlot.rebind_consume
