import LeanPoo.Functional.CertifiedConsumer
import LeanPoo.Functional.ResultView

namespace LeanPoo.Tests.FunctionalCertifiedConsumer
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


/- A real Type-valued output packs quantities and three admitted constraints.
The client constructs this from data/proof, without provider requires. -/
private structure Output (c : Nat) where
  amount : Nat
  limit : Nat
  remaining : Nat
  enabled : Bool
  lower : c ≤ amount
  balanced : amount + remaining = limit
  active : enabled = true
private def construct (c : Nat) (data : Results Value c jointKeys) (proof : Joint c data) : Output c where
  amount := data.1.val
  limit := data.2.1
  remaining := Nat.sub data.2.1 data.1.val
  enabled := data.2.2.1
  lower := data.1.property
  balanced := Nat.add_sub_of_le proof.1
  active := proof.2.1

/- Named dependent data access is available inside a constructor. -/
example (c : Nat) (data : Results Value c jointKeys) (proof : Joint c data) :
    (construct c data proof).amount = (resultAt data Key.quantity (by simp [jointKeys])).val := rfl
example (ready : Certified jointKeys Joint) (c : Nat) :
    (ready.consume construct c).amount + (ready.consume construct c).remaining =
      (ready.consume construct c).limit := (ready.consume construct c).balanced

#eval do
  let mut successful := 0
  for mask in List.range 8 do
    match prepareCertified (provider mask) jointKeys Joint (joint_admit mask) with
    | .error key =>
      unless some key == jointKeys.find? (fun key => !(available mask key)) do
        throw (IO.userError "consumer first missing key")
    | .ok ready =>
      let run := ready.consume construct
      for c in [0, 7, 23] do
        let output := run c
        unless output.amount == c+1 && output.limit == c+2 && output.remaining == 1 &&
            output.enabled && output.amount + output.remaining == output.limit do
          throw (IO.userError "independent output model mismatch")
      successful := successful+1
  unless successful == 1 do throw (IO.userError "availability coverage")
  IO.println "FUNCTIONAL-CERTIFIED-CONSUMER-OUTPUT-OK masks=8 outputs=3"

/- Whole-tuple equality is a joint contract for arbitrary order/repeats. -/
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
private def check (mask : Nat) (keys : List Key) : IO Nat := do
  let Claim := fun c data => data = expected c keys
  let construct := fun c data (_ : Claim c data) => score c keys data
  match prepareConsumer (provider mask) keys Claim (selected_expected mask keys) construct with
  | .error key =>
    unless some key == keys.find? (fun key => !(available mask key)) do
      throw (IO.userError "scalar consumer first error")
    return 0
  | .ok run =>
    for c in [0, 7, 23] do
      unless run c == scalar c keys do throw (IO.userError "scalar consumer mismatch")
    return 1
#eval do
  let mut cases := 0
  let mut successful := 0
  for mask in List.range 8 do
    for requested in List.range 8 do
      let keys := requests requested
      for keys in [keys, keys.reverse, keys ++ keys] do
        successful := successful + (← check mask keys)
        cases := cases+1
  IO.println s!"FUNCTIONAL-CERTIFIED-CONSUMER-OK cases={cases} successful={successful} contexts=3"

/- The generic replacement theorem preserves arbitrary proof-aware consumers. -/
example {Context Key : Type} {Value Other PublicValue : Context → Key → Type}
    (keys : List Key) (expose : ∀ c key, Value c key → PublicValue c key)
    (reveal : ∀ c key, Other c key → PublicValue c key)
    (Claim : ∀ c, Results PublicValue c keys → Prop)
    (ready : Certified keys (fun c data => Claim c (observeResults expose data)))
    (candidate : Factories Context Other keys)
    (same : Related (fun c key a b => expose c key a = reveal c key b) keys ready.factories candidate)
    {Output : Context → Type} (construct : ∀ c data, Claim c data → Output c) :
    (ready.observe expose Claim (fun _ _ proof => proof)).consume construct =
      ((Certified.replaceObserved keys expose reveal Claim ready candidate same).observe
        reveal Claim (fun _ _ proof => proof)).consume construct :=
  Certified.consume_observed keys expose reveal Claim ready candidate same construct

/- An invalid cross-capability budget cannot supply the required certificate. -/
example (c : Nat) (data : Results Value c jointKeys) (tooSmall : Nat.lt data.2.1 data.1.val) :
    ¬ Joint c data := fun proof => Nat.not_le_of_gt tooSmall proof.1

/- A Prop-only existence theorem is not an executable Type-level witness. -/
example (_exists : ∃ n : Nat, n = 3) : True := by
  fail_if_success
    have _witness : Nat := Exists.elim _exists (fun n _ => n)
  trivial

example (_ready : Certified jointKeys Joint) : True := by
  fail_if_success
    have _wrong : Output 9 := _ready.consume construct 0
  trivial
#print axioms Certified.consume_apply
#print axioms Certified.consume_congr
#print axioms Certified.consume_observed

#print axioms prepareConsumer_error_iff
