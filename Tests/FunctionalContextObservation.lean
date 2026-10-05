import LeanPoo.Functional.ContextObservation

namespace LeanPoo.Tests.FunctionalContextObservation
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


private def Other (c : Nat) (key : Key) := Value c key × Bool
private def expose : ∀ c key, Value c key → Value c key := fun _ _ value => value
private def reveal : ∀ c key, Other c key → Value c key := fun _ _ value => value.1
private def alternate (mask : Nat) : Provider Nat Key Other :=
  fun key => if available mask key then some (fun c => (source key c, false)) else none
private theorem compatible (mask other : Nat) (keys : List Key) :
    RelatedOn (provider mask) (alternate other) keys (fun c key a b => expose c key a = reveal c key b) := by
  intro key member left right first second c
  have a : available mask key = true := by
    cases found : available mask key <;> simp [provider, found] at first ⊢
  have b : available other key = true := by
    cases found : available other key <;> simp [alternate, found] at second ⊢
  have old : source key = left := by simpa [provider, a] using first
  have new : (fun c => (source key c, false) : Factory Nat (fun c => Other c key)) = right := by
    apply Option.some.inj
    simpa [alternate, b, Other] using second
  rw [← old, ← new]
  rfl

private def requests (mask : Nat) : List Key :=
  [Key.quantity, .limit, .enabled].filter (available mask)
private def equalResults (c : Nat) : (keys : List Key) → Results Value c keys → Results Value c keys → Bool
  | [], _, _ => true
  | .quantity :: rest, (a, tail), (b, remaining) => a.val == b.val && equalResults c rest tail remaining
  | .limit :: rest, (a, tail), (b, remaining) => (@BEq.beq Nat inferInstance a b) && equalResults c rest tail remaining
  | .enabled :: rest, (a, tail), (b, remaining) => (@BEq.beq Bool inferInstance a b) && equalResults c rest tail remaining
private def check (mask other : Nat) (keys : List Key) : IO Nat := do
  let Public := fun c data => data = expected c keys
  let Claim := fun c data => Public c (observeResults expose data)
  have admit : ∀ factories, Selected (provider mask) keys factories →
      ∀ c, Claim c (build factories c) := by
    intro factories selected c
    rw [selected_expected mask keys factories selected c]
    exact observeResults_id _
  let old := prepareCertified (provider mask) keys Claim admit
  let fresh := prepare (alternate other) keys
  let expectedOld := keys.find? (fun key => !(available mask key))
  let expectedNew := keys.find? (fun key => !(available other key))
  match oldReady : old, freshReady : fresh, expectedOld, expectedNew with
  | .error key, _, some missing, _ =>
    unless key == missing do throw (IO.userError "old first error")
    match fresh, expectedNew with
    | .error key, some missing => unless key == missing do throw (IO.userError "candidate first error")
    | .ok _, none => pure ()
    | _, _ => throw (IO.userError "candidate availability mismatch")
    return 0
  | .ok _, .error key, none, some missing =>
    unless key == missing do throw (IO.userError "candidate first error")
    return 0
  | .ok ready, .ok candidate, none, none =>
    have selected : Selected (alternate other) keys candidate := by
      exact (prepare_ok_iff _ _ _).mp freshReady
    have oldSelected : Selected (provider mask) keys ready.factories := by
      have aligned := prepareCertified_forget (provider mask) keys Claim admit
      change old.map Certified.factories = prepare (provider mask) keys at aligned
      rw [oldReady] at aligned
      exact (prepare_ok_iff _ _ _).mp aligned.symm
    let replacement := Certified.replaceObserved keys expose reveal Public ready candidate
      (selected_related _ _ _ keys ready.factories candidate oldSelected selected (compatible mask other keys))
    let visible :=  replacement.observe reveal Public (fun _ _ proof => proof)
    let relation := selected_related _ _ _ keys ready.factories candidate oldSelected selected
      (compatible mask other keys)
    for c in [0, 7, 23] do
      let empty := (ContextSlot.empty ready).observe expose Public (fun _ _ proof => proof)
      let (emptyData, _, emptyHit) := empty.read c
      let (_, broad, _) := (ContextSlot.empty ready).read c
      let exposedSlot := broad.observe expose Public (fun _ _ proof => proof)
      let (data, _, hit) := exposedSlot.read c
      let transferred := broad.replaceObservedPublic expose reveal Public candidate relation
      let (replacementData, same, replacementHit) := transferred.read c
      let (changed, next, changeHit) := same.read (c+1)
      let (returned, _, returnHit) := next.read c
      let (_, hidden, _) := (ContextSlot.empty replacement).read c
      let (exposed, _, exposedHit) := (hidden.observe reveal Public (fun _ _ proof => proof)).read c
      unless !emptyHit && hit && replacementHit && !changeHit && !returnHit && exposedHit do
        throw (IO.userError "observation/replacement hit policy mismatch")
      unless equalResults c keys emptyData.val (expected c keys) &&
          equalResults c keys data.val (expected c keys) &&
          equalResults c keys replacementData.val (expected c keys) &&
          equalResults (c+1) keys changed.val (expected (c+1) keys) &&
          equalResults c keys returned.val (expected c keys) &&
          equalResults c keys exposed.val (expected c keys) &&
          equalResults c keys replacementData.val (visible.build c).val do
        throw (IO.userError "public cached/uncached/independent mismatch")
    return 1
  | _, _, _, _ => throw (IO.userError "source availability mismatch")

#eval do
  let mut cases := 0
  let mut replaced := 0
  for mask in List.range 8 do
    for other in List.range 8 do
      for requested in List.range 8 do
        let keys := requests requested
        for keys in [keys, keys.reverse, keys ++ keys] do
          replaced := replaced + (← check mask other keys)
          cases := cases+1
  IO.println s!"FUNCTIONAL-CONTEXT-OBSERVATION-OK cases={cases} replaced={replaced} contexts=3 reads={replaced*18} hits={replaced*9}"

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

#eval do
  let mut joint := 0
  for other in List.range 8 do
    match oldReady : prepareCertified (provider 7) jointKeys Joint (joint_admit 7),
        freshReady : prepare (alternate other) jointKeys with
    | .ok ready, .ok candidate =>
      have oldSelected : Selected (provider 7) jointKeys ready.factories := by
        have aligned := prepareCertified_forget (provider 7) jointKeys Joint (joint_admit 7)
        rw [oldReady] at aligned
        exact (prepare_ok_iff _ _ _).mp aligned.symm
      let proofReady : Certified jointKeys (fun c data => Joint c (observeResults expose data)) :=
        ⟨ready.factories, fun c => by
          change Joint c (build ready.factories c)
          exact ready.valid c⟩
      let relation := selected_related _ _ _ jointKeys _ _ oldSelected
        ((prepare_ok_iff _ _ _).mp freshReady) (compatible 7 other jointKeys)
      for c in [0, 7, 23] do
        let (_, broad, _) := (ContextSlot.empty proofReady).read c
        let small := broad.replaceObservedPublic expose reveal Joint candidate relation
        let construct := fun _ data (_ : Joint _ data) => Nat.sub data.2.1 data.1.val
        let (remaining, _, hit) := small.consume construct c
        unless hit && remaining == 1 do throw (IO.userError "joint public cache consumer")
      joint := joint+1
    | .ok _, .error key =>
      unless some key == jointKeys.find? (fun key => !(available other key)) do
        throw (IO.userError "joint candidate error mismatch")
    | .error _, _ => throw (IO.userError "full original unavailable")
  unless joint == 1 do throw (IO.userError "joint availability coverage")
  IO.println "FUNCTIONAL-CONTEXT-OBSERVATION-JOINT-OK candidates=8 replaced=1 contexts=3"

/- A visible change cannot be admitted by hidden-metadata equivalence. -/
private def changed : Provider Nat Key Other
  | .quantity => some (fun c => (⟨c+2, by omega⟩, false))
  | key => alternate 7 key
example : ¬ RelatedOn (provider 7) changed [Key.quantity]
    (fun c key a b => expose c key a = reveal c key b) := by
  intro same
  have disagree := same .quantity (by simp) _ _ rfl rfl 0
  have bad := congrArg (fun value : Value 0 .quantity => value.val) disagree
  change (1 : Nat) = 2 at bad
  omega
/- Observed caches cannot be used as replacement hidden data. -/
example (old : Certified [Key.quantity] (fun _ (_ : Results Other _ [Key.quantity]) => True))
    (slot : ContextSlot old) : True := by
  let observed := slot.observe reveal (fun _ _ => True) (fun _ _ _ => True.intro)
  fail_if_success have _hidden : ContextSlot old := observed
  trivial
/- Context indices remain exact after public observation. -/
example (old : Certified [Key.quantity] (fun _ (_ : Results Other _ [Key.quantity]) => True))
    (_snapshot : Snapshot old 0) : True := by
  fail_if_success have _wrong : Snapshot old 9 := _snapshot
  trivial
#print axioms Snapshot.observe_val
#print axioms ContextSlot.observe_empty
#print axioms ContextSlot.observe_retained
#print axioms ContextSlot.observe_hit
#print axioms ContextSlot.observe_consume
#print axioms ContextSlot.replaceObservedPublic_consume
