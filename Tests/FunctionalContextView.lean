import LeanPoo.Functional.ContextView

namespace LeanPoo.Tests.FunctionalContextView
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
    let derive := fun (_ : Nat) data (same : Claim _ data) =>
      congrArg (fun data => projectResults data keys included) same
    let view := ready.projectData keys included Narrow derive
    for c in [0, 7, 23] do
      let empty := (ContextSlot.empty ready).project keys included Narrow derive
      let (emptyData, _, emptyHit) := empty.read c
      let (_, broad, _) := (ContextSlot.empty ready).read c
      let small := broad.project keys included Narrow derive
      let (data, same, hit) := small.read c
      let (changed, next, changeHit) := same.read (c+1)
      let (returned, _, returnHit) := next.read c
      let identity : ∀ key ∈ keys, key ∈ keys := fun _ h => h
      let twice := same.project keys identity (fun _ _ => True) (fun _ _ _ => True.intro)
      let (again, _, againHit) := twice.read c
      unless !emptyHit && hit && !changeHit && !returnHit && againHit do
        throw (IO.userError "projected hit/miss/eviction mismatch")
      unless equalResults c keys emptyData.val (expected c keys) &&
          equalResults c keys data.val (expected c keys) &&
          equalResults (c+1) keys changed.val (expected (c+1) keys) &&
          equalResults c keys returned.val (expected c keys) &&
          equalResults c keys again.val (expected c keys) &&
          equalResults c keys data.val (view.build c).val do
        throw (IO.userError "projected cache independent/uncached mismatch")
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
  IO.println s!"FUNCTIONAL-CONTEXT-VIEW-OK cases={cases} successes={successes} contexts=3 reads={successes*15} hits={successes*6}"

/- A value-level joint bound survives reordered cached data and construction. -/
private def pairKeys : List Key := [.quantity, .limit]
private def bound (c : Nat) (data : Results Value c pairKeys) := data.1.val ≤ data.2.1
#eval do
  let ready : Certified pairKeys bound :=
    ⟨(source .quantity, source .limit, PUnit.unit), fun c => by simp [bound, pairKeys, build, source]⟩
  let keys : List Key := [.limit, .quantity]
  let included : ∀ key ∈ keys, key ∈ pairKeys := by
    intro key member
    cases key <;> simp_all [keys, pairKeys]
  let Narrow := fun c (data : Results Value c keys) => data.2.1.val ≤ data.1
  let derive : ∀ c data, bound c data → Narrow c (projectResults data keys included) := by
    intro c data proof
    exact proof
  for c in [0,7,23] do
    let (_, broad, _) := (ContextSlot.empty ready).read c
    let small := broad.project keys included Narrow derive
    let construct := fun _ data (_ : Narrow _ data) => Nat.sub data.1 data.2.1.val
    let (remaining, _, hit) := small.consume construct c
    unless hit && remaining == 1 do throw (IO.userError "joint proof consumer")
  IO.println "FUNCTIONAL-CONTEXT-VIEW-JOINT-OK reordered=3"

/- Duplicate source positions can differ: the first named occurrence wins. -/
#eval do
  let keys : List Key := [.limit, .limit]
  let ready : Certified (Value := Value) keys (fun _ _ => True) :=
    ⟨(fun _ => (11 : Nat), fun _ => (99 : Nat), PUnit.unit), fun _ => True.intro⟩
  let (_, slot, _) := (ContextSlot.empty ready).read 7
  let small := slot.project [Key.limit, .limit] (by simp [keys])
    (fun _ _ => True) (fun _ _ _ => True.intro)
  let (data, _, hit) := small.read 7
  unless hit && (@BEq.beq Nat inferInstance data.val.1 11) &&
      (@BEq.beq Nat inferInstance data.val.2.1 11) do
    throw (IO.userError "cached duplicate did not select first")
  IO.println "FUNCTIONAL-CONTEXT-VIEW-DUPLICATE-OK first=11 later=99"

/- Distinct dependent context indices cannot be interchanged after projection. -/
example (ready : Certified (Value := Value) [Key.quantity] (fun _ _ => True))
    (_snapshot : Snapshot ready 0) : True := by
  fail_if_success have _wrong : Snapshot ready 9 := _snapshot
  trivial
/- A missing key cannot be made available by projection. -/
example : True := by
  fail_if_success have _missing : ∀ key ∈ [Key.enabled], key ∈ [Key.quantity] := by simp
  trivial
#print axioms Snapshot.project_val
#print axioms ContextSlot.project_empty
#print axioms ContextSlot.project_retained
#print axioms ContextSlot.project_hit
#print axioms ContextSlot.project_consume
