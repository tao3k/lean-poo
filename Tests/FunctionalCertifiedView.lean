import LeanPoo.Functional.CertifiedView

namespace LeanPoo.Tests.FunctionalCertifiedView
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


private def broad : List Key := [.quantity, .limit, .enabled]
private def small : List Key := [.quantity, .quantity]
private def Broad (c : Nat) (data : Results Value c broad) : Prop := data = expected c broad
private def Small (c : Nat) (data : Results Value c small) : Prop :=
  data.1.val = c+1 ∧ data.2.1 = data.1
private theorem included : ∀ key ∈ small, key ∈ broad := by
  intro key member
  simp [small] at member
  subst key
  simp [broad]
private theorem derive (ready : Certified broad Broad) (c : Nat)
    (valid : Broad c (build ready.factories c)) :
    Small c (build (project ready.factories small included) c) := by
  rcases ready with ⟨⟨quantity, limit, enabled, tail⟩, proof⟩
  have same : quantity c = source .quantity c := congrArg Prod.fst valid
  simp [Small, small, broad, project, factoryAt, build, same, source]
  rfl
private theorem admit (mask : Nat) (factories : Factories Nat Value small)
    (selected : Selected (provider mask) small factories) :
    ∀ c, Small c (build factories c) := by
  intro c
  rw [selected_expected mask small factories selected c]
  simp [Small, small, expected, source]
  rfl

/- Generic complete outcome equality, including fallback errors. -/
example (mask : Nat) (cache : CachedPreparation (provider mask) broad Broad) :
    (cache.narrow (provider mask) broad small Broad Small included derive (admit mask)).outcome =
      prepareCertified (provider mask) small Small (admit mask) :=
  cache.narrow_eq (provider mask) broad small Broad Small included derive (admit mask)

#eval do
  let mut successes := 0
  let mut rescued := 0
  for mask in List.range 8 do
    let cache := cacheCertified (provider mask) broad Broad (selected_expected mask broad)
    let narrow := cache.narrow (provider mask) broad small Broad Small included derive (admit mask)
    match narrow.outcome with
    | .error key =>
      unless key == Key.quantity && !(available mask .quantity) do
        throw (IO.userError "wrong narrow first error")
    | .ok ready =>
      unless available mask .quantity do throw (IO.userError "missing quantity admitted")
      successes := successes+1
      if mask != 7 then rescued := rescued+1
      for c in [0, 7, 23] do
        let data := (ready.build c).val
        unless data.1.val == c+1 && data.2.1.val == data.1.val do
          throw (IO.userError "duplicate certified projection mismatch")
    /- Empty consumers must succeed even when the broad cache failed. -/
    let empty := cache.narrow (provider mask) broad [] Broad (fun _ _ => True)
      (by simp) (fun _ _ _ => True.intro) (fun _ _ _ => True.intro)
    match empty.outcome with
    | .ok _ => pure ()
    | .error _ => throw (IO.userError "broad failure poisoned empty consumer")
    /- Narrow order controls the first error, independently of broad order. -/
    let reversed := cache.narrow (provider mask) broad [Key.enabled, .limit] Broad
      (fun _ _ => True) (by simp [broad]) (fun _ _ _ => True.intro) (fun _ _ _ => True.intro)
    let missing := [Key.enabled, .limit].find? (fun key => !(available mask key))
    match reversed.outcome, missing with
    | .error key, some expected =>
      unless key == expected do throw (IO.userError "broad error/order leaked into consumer")
    | .ok ready, none =>
      for c in [0, 7, 23] do
        let data := (ready.build c).val
        unless data.1 && (@BEq.beq Nat inferInstance data.2.1 (c+2)) do throw (IO.userError "reordered tuple mismatch")
    | _, _ => throw (IO.userError "reordered availability mismatch")
  unless successes == 4 && rescued == 3 do throw (IO.userError "coverage mismatch")
  IO.println s!"FUNCTIONAL-CERTIFIED-VIEW-OK masks=8 requests=24 successes={successes} rescued={rescued} contexts=3"

/- A joint certificate alone does not establish an arbitrary narrow claim. -/
example (_ready : Certified broad Broad) : True := by
  fail_if_success
    have _wrong : Certified small (fun _ _ => False) :=
      _ready.project small included (fun _ _ => False) (fun _ h => h)
  trivial
#print axioms Certified.project_factories
#print axioms CachedPreparation.narrow_eq

#print axioms CachedPreparation.narrow_of_ok
