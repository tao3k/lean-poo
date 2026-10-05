import LeanPoo.Functional.ResultView

namespace LeanPoo.Tests.FunctionalResultView
open Functional Requirements
private inductive Key where
  | quantity | limit | enabled
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq
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
private def equalResults (c : Nat) : (keys : List Key) → Results Value c keys → Results Value c keys → Bool
  | [], _, _ => true
  | .quantity :: rest, (a, tail), (b, remaining) => a.val == b.val && equalResults c rest tail remaining
  | .limit :: rest, (a, tail), (b, remaining) => (@BEq.beq Nat inferInstance a b) && equalResults c rest tail remaining
  | .enabled :: rest, (a, tail), (b, remaining) => (@BEq.beq Bool inferInstance a b) && equalResults c rest tail remaining

private def check (mask : Nat) (sourceKeys keys : List Key)
    (included : ∀ key ∈ keys, key ∈ sourceKeys) : IO Nat := do
  let Claim := fun c data => data = expected c sourceKeys
  let Narrow := fun c data => data = projectResults (expected c sourceKeys) keys included
  match prepareCertified (provider mask) sourceKeys Claim (selected_expected mask sourceKeys) with
  | .error actual =>
    unless some actual == sourceKeys.find? (fun key => !(available mask key)) do
      throw (IO.userError "wrong source error")
    return 0
  | .ok ready =>
    let view := ready.projectData keys included Narrow
      (fun _ _ same => congrArg (fun data => projectResults data keys included) same)
    for c in [0, 7, 23] do
      let built := ready.build c
      let evidence := projectEvidence built keys included (Narrow c)
        (fun _ same => congrArg (fun data => projectResults data keys included) same)
      let projected := evidence.val
      unless equalResults c keys projected (expected c keys) &&
          equalResults c keys (view.build c).val (expected c keys) do
        throw (IO.userError "independent scalar projection mismatch")
    return 1

#eval do
  let mut cases := 0
  let mut successes := 0
  for mask in List.range 8 do
    for sourceMask in List.range 8 do
      let selected := requests sourceMask
      for sourceKeys in ([selected, selected.reverse, selected ++ selected] : List (List Key)) do
        for targetMask in List.range 8 do
          let retained := (requests targetMask).filter (fun key => List.contains (sourceKeys : List Key) key)
          have subset : ∀ key ∈ retained, key ∈ sourceKeys := by
            intro key member
            exact List.contains_iff_mem.mp (List.mem_filter.mp member).2
          successes := successes + (← check mask sourceKeys retained subset)
          successes := successes + (← check mask sourceKeys retained.reverse
            (fun key member => subset key (List.mem_reverse.mp member)))
          successes := successes + (← check mask sourceKeys (retained ++ retained)
            (fun key member => (List.mem_append.mp member).elim (subset key) (subset key)))
          cases := cases+3
  IO.println s!"FUNCTIONAL-RESULT-VIEW-OK cases={cases} successes={successes} contexts=3"

/- Arbitrary tuples need not agree at duplicate positions: choose the first. -/
private def repeated : List Key := [.limit, .limit]
example (c : Nat) : resultAt (Value := Value) (context := c)
    (keys := repeated) ((11 : Nat), (99 : Nat), PUnit.unit) Key.limit (by simp [repeated]) = (11 : Nat) := by
  rfl
#eval do
  let factories : Factories Nat Value repeated := (fun _ => (11 : Nat), fun _ => (99 : Nat), PUnit.unit)
  let projected := project factories [.limit, .limit] (by simp [repeated])
  let built := build projected 7
  unless (@BEq.beq Nat inferInstance built.1 11) &&
      (@BEq.beq Nat inferInstance built.2.1 11) do
    throw (IO.userError "duplicate projection used later occurrence")
  IO.println "FUNCTIONAL-RESULT-VIEW-DUPLICATE-OK first=11 later=99"

/- The key preserves its dependent value contract without tuple positions. -/
example (c : Nat) (data : Results Value c [.enabled, .quantity, .limit]) :
    c ≤ (resultAt data Key.quantity (by simp)).val :=
  (resultAt data Key.quantity (by simp)).property

example (_data : Results Value 0 [.quantity]) : True := by
  fail_if_success
    have _wrong : Value 9 .quantity := resultAt _data Key.quantity (by simp)
  trivial
#print axioms resultAt_build
#print axioms build_project
#print axioms Certified.projectData_factories
#print axioms Certified.projectData_build

#print axioms projectEvidence_val
