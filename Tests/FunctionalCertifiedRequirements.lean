import LeanPoo.Functional.CertifiedRequirements

namespace LeanPoo.Tests.FunctionalCertifiedRequirements
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

/- A complete joint contract relates two different capability result types and
requires a third value; duplicate quantity requests retain their order. -/
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

/- A client reads a data-indexed proof without handwritten capability requires. -/
example (ready : Certified jointKeys Joint) (c : Nat) :
    (ready.build c).val.1.val ≤ (ready.build c).val.2.1 :=
  (ready.build c).property.1

/- Generic old joint evidence remains usable after an exact selection change. -/
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    (keys : List Key) (Claim : ∀ c, Results Value c keys → Prop)
    (left right : Provider Context Key Value)
    (admit : ∀ f, Selected left keys f → ∀ c, Claim c (build f c))
    (otherAdmit : ∀ f, Selected right keys f → ∀ c, Claim c (build f c))
    (same : ∀ key ∈ keys, right key = left key) :
    prepareCertified right keys Claim otherAdmit = prepareCertified left keys Claim admit :=
  prepareCertified_congr left right keys Claim admit otherAdmit (prepare_congr left right keys same)

private def requests (mask : Nat) : List Key :=
  [Key.quantity, .limit, .enabled].filter (available mask)
private def equalResults (c : Nat) : (keys : List Key) → Results Value c keys → Results Value c keys → Bool
  | [], _, _ => true
  | .quantity :: rest, (a, tail), (b, remaining) => a.val == b.val && equalResults c rest tail remaining
  | .limit :: rest, (a, tail), (b, remaining) => (@BEq.beq Nat inferInstance a b) && equalResults c rest tail remaining
  | .enabled :: rest, (a, tail), (b, remaining) => (@BEq.beq Bool inferInstance a b) && equalResults c rest tail remaining
private def check (mask : Nat) (keys : List Key) : IO Unit := do
  let claim := fun c data => data = expected c keys
  let outcome := prepareCertified (provider mask) keys claim (selected_expected mask keys)
  let missing := keys.find? (fun key => !(available mask key))
  match outcome, missing with
  | .error actual, some key => unless actual == key do throw (IO.userError "wrong first missing key")
  | .ok ready, none =>
    for c in [0, 7, 23] do
      unless equalResults c keys (ready.build c).val (expected c keys) do
        throw (IO.userError "wrong typed tuple")
  | _, _ => throw (IO.userError "availability mismatch")
#eval do
  let mut cases := 0
  for mask in List.range 8 do
    for requested in List.range 8 do
      let keys := requests requested
      for keys in [keys, keys.reverse, keys ++ keys] do
        check mask keys
        cases := cases+1
    match prepareCertified (provider mask) jointKeys Joint (joint_admit mask) with
    | .error key =>
      unless some key == jointKeys.find? (fun key => !(available mask key)) do
        throw (IO.userError "joint first error")
    | .ok ready =>
      for c in [0, 7, 23] do
        let data := (ready.build c).val
        unless Nat.ble data.1.val data.2.1 && data.2.2.1 && data.2.2.2.1.val == data.1.val do
          throw (IO.userError "joint contract scalar mismatch")
  IO.println s!"FUNCTIONAL-CERTIFIED-REQUIREMENTS-OK preparations={cases} joint=8 contexts=3"

/- Context/type alignment remains a real obligation. -/
example (_ready : Certified jointKeys Joint) : True := by
  fail_if_success have _wrong : Results Value 9 jointKeys := (_ready.build 0).val
  trivial
#print axioms Certified.build_val
#print axioms prepareCertified_forget
#print axioms Certified.ext
#print axioms Certified.forget_injective
#print axioms prepareCertified_error_iff
#print axioms prepareCertified_congr
end LeanPoo.Tests.FunctionalCertifiedRequirements
