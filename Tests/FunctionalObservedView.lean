import LeanPoo.Functional.ObservedView

namespace LeanPoo.Tests.FunctionalObservedView
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
private def PublicValue (_ : Nat) (_ : Key) := Nat
private def expose : ∀ c key, Value c key → PublicValue c key
  | _, .quantity, value => value.val*2
  | _, .limit, value => Nat.add value 10
  | _, .enabled, value => cond value (1 : Nat) (0 : Nat)
private def publicExpected (c : Nat) : (keys : List Key) → Results PublicValue c keys
  | [] => PUnit.unit
  | key :: rest => ((match key with
      | .quantity => 2*(c+1) | .limit => c+12 | .enabled => (1 : Nat)), publicExpected c rest)
private def equalPublic (c : Nat) : (keys : List Key) → Results PublicValue c keys → Results PublicValue c keys → Bool
  | [], _, _ => true
  | _ :: rest, (a, tail), (b, remaining) => (@BEq.beq Nat inferInstance a b) && equalPublic c rest tail remaining
private def sumPublic (c : Nat) : (keys : List Key) → Results PublicValue c keys → Nat
  | [], _ => 0
  | _ :: rest, (head, tail) => Nat.add head (sumPublic c rest tail)
private def check (mask : Nat) (sourceKeys keys : List Key)
    (included : ∀ key ∈ keys, key ∈ sourceKeys) : IO Nat := do
  let Claim := fun c data => data = expected c sourceKeys
  let Public := fun c data => data = observeResults expose (projectResults (expected c sourceKeys) keys included)
  let derive := fun (_ : Nat) data (same : Claim _ data) =>
    congrArg (fun data => observeResults expose (projectResults data keys included)) same
  match prepareCertified (provider mask) sourceKeys Claim (selected_expected mask sourceKeys) with
  | .error actual =>
    unless some actual == sourceKeys.find? (fun key => !(available mask key)) do
      throw (IO.userError "first missing capability mismatch")
    return 0
  | .ok ready =>
    for c in [0,7,23] do
      let (_, broad, _) := (ContextSlot.empty ready).read c
      let view := broad.observeProject keys included expose Public derive
      let (data, next, hit) := view.read c
      let (changed, moved, changeHit) := next.read (c+1)
      let (returned, _, returnHit) := moved.read c
      let (emptyData, _, emptyHit) := ((ContextSlot.empty ready).observeProject keys included expose Public derive).read c
      unless hit && !changeHit && !returnHit && !emptyHit do
        throw (IO.userError "fused cache policy mismatch")
      let broadObserved := observeResults expose (build ready.factories c)
      let oldOrdering := projectResults broadObserved keys included
      let uncached := build (ready.observeProject keys included expose Public derive).factories c
      unless equalPublic c keys data.val (publicExpected c keys) &&
          equalPublic c keys data.val oldOrdering && equalPublic c keys data.val uncached &&
          equalPublic (c+1) keys changed.val (publicExpected (c+1) keys) &&
          equalPublic c keys returned.val (publicExpected c keys) &&
          equalPublic c keys emptyData.val (publicExpected c keys) do
        throw (IO.userError "fused/broad-first/uncached/independent mismatch")
      let construct := fun c data (_ : Public c data) => sumPublic c keys data
      let (output, _, _) := view.consume construct c
      unless output == sumPublic c keys (publicExpected c keys) do
        throw (IO.userError "public constructor mismatch")
    return 1
#eval do
  let mut cases := 0
  let mut successes := 0
  for mask in List.range 8 do
    for sourceMask in List.range 8 do
      let selected := requests sourceMask
      for sourceKeys in [selected, selected.reverse, selected ++ selected] do
        for targetMask in List.range 8 do
          let retained := (requests targetMask).filter (fun key => List.contains sourceKeys key)
          have subset : ∀ key ∈ retained, key ∈ sourceKeys := by
            intro key member
            exact List.contains_iff_mem.mp (List.mem_filter.mp member).2
          successes := successes + (← check mask sourceKeys retained subset)
          successes := successes + (← check mask sourceKeys retained.reverse
            (fun key member => subset key (List.mem_reverse.mp member)))
          successes := successes + (← check mask sourceKeys (retained ++ retained)
            (fun key member => (List.mem_append.mp member).elim (subset key) (subset key)))
          cases := cases+3
  unless cases == 4608 && successes == 1944 do throw (IO.userError "coverage mismatch")
  IO.println s!"FUNCTIONAL-OBSERVED-VIEW-OK cases={cases} successes={successes} contexts=3 reads={successes*12} hits={successes*3}"

#eval do
  let keys : List Key := [.limit, .limit]
  let ready : Certified (Value := Value) keys (fun _ _ => True) :=
    ⟨(fun _ => (11 : Nat), fun _ => (99 : Nat), PUnit.unit), fun _ => True.intro⟩
  let (_, slot, _) := (ContextSlot.empty ready).read 7
  let small := slot.observeProject [Key.limit, .limit] (by simp [keys]) expose
    (fun _ _ => True) (fun _ _ _ => True.intro)
  let (data, _, hit) := small.read 7
  unless hit && (@BEq.beq Nat inferInstance data.val.1 21) &&
      (@BEq.beq Nat inferInstance data.val.2.1 21) do
    throw (IO.userError "observed duplicate used later value")
  IO.println "FUNCTIONAL-OBSERVED-VIEW-DUPLICATE-OK first=21 later=109"
private def pairKeys : List Key := [.quantity, .limit]
private def Bound (c : Nat) (data : Results Value c pairKeys) := data.1.val ≤ data.2.1
private def reveal : ∀ c key, Value c key → PublicValue c key
  | _, .quantity, value => value.val
  | _, .limit, value => value
  | _, .enabled, value => cond value (1 : Nat) (0 : Nat)
#eval do
  let ready : Certified pairKeys Bound :=
    ⟨(source .quantity, source .limit, PUnit.unit), fun c => by simp [Bound, pairKeys, build, source]⟩
  let keys : List Key := [.limit, .quantity]
  let included : ∀ key ∈ keys, key ∈ pairKeys := by
    intro key member
    cases key <;> simp_all [keys, pairKeys]
  let Public := fun c (data : Results PublicValue c keys) => Nat.le data.2.1 data.1
  let derive : ∀ c data, Bound c data → Public c (observeResults reveal (projectResults data keys included)) := by
    intro c data proof
    exact proof
  for c in [0,7,23] do
    let (_, broad, _) := (ContextSlot.empty ready).read c
    let small := broad.observeProject keys included reveal Public derive
    let construct := fun (c : Nat) (data : Results PublicValue c keys) (proof : Public c data) =>
      (⟨data, ⟨Nat.sub data.1 data.2.1, Nat.sub_add_cancel proof⟩⟩ :
        (data : Results PublicValue c keys) × {n : Nat // Nat.add n data.2.1 = data.1})
    let (output, _, hit) := small.consume construct c
    unless hit && output.2.val == 1 do throw (IO.userError "public joint proof output")
  IO.println "FUNCTIONAL-OBSERVED-VIEW-JOINT-OK contexts=3"
example (ready : Certified (Value := Value) [Key.quantity] (fun _ _ => True))
    (_data : Snapshot ready 0) : True := by
  fail_if_success have _wrong : Snapshot ready 9 := _data
  trivial
example : True := by
  fail_if_success have _missing : ∀ key ∈ [Key.enabled], key ∈ [Key.quantity] := by simp
  trivial
#print axioms resultAt_observe
#print axioms projectResults_observe
#print axioms Snapshot.observeProject_val
#print axioms ContextSlot.observeProject_empty
#print axioms ContextSlot.observeProject_retained
#print axioms ContextSlot.observeProject_hit
#print axioms ContextSlot.observeProject_consume
