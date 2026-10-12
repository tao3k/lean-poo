import LeanPoo.Functional.SharedViews
import LeanPoo.Functional.ViewRetarget

/-! Billing and monitoring share one broad dependency read. A representation
replacement then preserves the billing interface and its warm public cache. -/
namespace LeanPoo.Examples.SharedReporting
open Functional Requirements

inductive Capability where
  | usage | capacity | secret | enabled
  deriving DecidableEq, Repr

def Value (context : Nat) : Capability → Type
  | .usage => {count : Nat // context ≤ count}
  | .capacity => Nat
  | .secret => String
  | .enabled => Bool

abbrev broad : List Capability := [.usage, .capacity, .usage, .secret, .enabled]
abbrev billed : List Capability := [.capacity, .usage]
abbrev monitored : List Capability := [.enabled, .usage, .usage]

def factories : Factories Nat Value broad :=
  (fun c => ⟨c+2, by omega⟩, fun c => c+5, fun c => ⟨c+99, by omega⟩,
    fun c => s!"private-{c}", fun c => c % 2 == 0, PUnit.unit)
def Joint (context : Nat) (data : Results Value context broad) : Prop :=
  data.1.val ≤ data.2.1 ∧ data.2.1 = context+5
def ready : Certified broad Joint := ⟨factories, fun _ => by simp [Joint, build, factories]⟩

def Public (_ : Nat) : Capability → Type
  | .usage | .capacity => Nat
  | .secret => Unit
  | .enabled => Bool
def expose : ∀ c key, Value c key → Public c key
  | _, .usage, value => value.val
  | _, .capacity, value => value
  | _, .secret, _ => ()
  | _, .enabled, value => value

def Billing (c : Nat) (data : Results Public c billed) : Prop := (show Nat from data.2.1) ≤ (show Nat from data.1) ∧ (show Nat from data.1) = c+5
def Monitoring (c : Nat) (data : Results Public c monitored) : Prop :=
  c ≤ data.2.1 ∧ data.2.1 = data.2.2.1
theorem billedIncluded : ∀ key ∈ billed, key ∈ broad := by intro key; cases key <;> simp [billed, broad]
theorem monitoredIncluded : ∀ key ∈ monitored, key ∈ broad := by intro key; cases key <;> simp [monitored, broad]

theorem billingProof (c : Nat) (data : Results Value c broad) (valid : Joint c data) :
    Billing c (observeResults expose (projectResults data billed billedIncluded)) := by
  change data.1.val ≤ data.2.1 ∧ data.2.1 = c+5
  exact valid
theorem monitoringProof (c : Nat) (data : Results Value c broad) (_valid : Joint c data) :
    Monitoring c (observeResults expose (projectResults data monitored monitoredIncluded)) := by
  simp only [Monitoring, projectResults, observeResults, expose, monitored]
  exact ⟨(resultAt data .usage (by simp [broad])).property, rfl⟩

structure Invoice (context : Nat) where
  amount : Nat
  capacity : Nat
  fits : amount ≤ capacity
  currentCapacity : capacity = context+5
  label : String

def invoice (label : String) (c : Nat) (data : Results Public c billed) (valid : Billing c data) : Invoice c :=
  ⟨data.2.1, data.1, valid.1, valid.2, label⟩
def bill (label : String) (c : Nat) (data : Snapshot ready c) : Invoice c :=
  data.consumeView billed billedIncluded expose Billing billingProof (invoice label)
def monitor (label : String) (c : Nat) (data : Snapshot ready c) : String :=
  data.consumeView monitored monitoredIncluded expose Monitoring monitoringProof
    (fun _ values _ =>
      let first : Nat := values.2.1
      let second : Nat := values.2.2.1
      let enabled : Bool := values.1
      s!"{label}:{first}/{second}:{cond enabled "on" "off"}")

-- The production representation changes key carriers and private metadata.
def Replacement (_ : Nat) : Capability → Type
  | .usage => Nat × String
  | .capacity => String × Nat
  | .secret => Nat
  | .enabled => Nat
def reveal : ∀ c key, Replacement c key → Public c key
  | _, .usage, value => value.1
  | _, .capacity, value => value.2
  | _, .secret, _ => ()
  | _, .enabled, value => (show Nat from value) != 0
def replacement : Factories Nat Replacement billed :=
  (fun c => ("encoded-limit", c+5), fun c => (c+2, "new-private-meter"), PUnit.unit)
theorem compatible : Related (fun c key a b => expose c key a = reveal c key b)
    billed (project ready.factories billed billedIncluded) replacement := by
  change (∀ c : Nat, c+5 = c+5) ∧ (∀ c : Nat, c+2 = c+2) ∧ True
  exact ⟨fun _ => rfl, fun _ => rfl, True.intro⟩

/-- Hidden replacement fields need no equality proof. Every billing consumer
keeps its proof-aware result for all contexts and all source cache states. -/
theorem billingRetargeted (slot : ContextSlot ready) (label : String) (c : Nat) :
    ((slot.retargetView billed billedIncluded expose reveal Billing billingProof replacement compatible).consume
      (invoice label) c).1 = (ready.observeProject billed billedIncluded expose Billing billingProof).consume
        (invoice label) c :=
  slot.retargetView_consume _ _ _ _ _ _ _ _ _ _

#eval do
  let mut slot := ContextSlot.empty ready
  let mut previous : Option Nat := none
  for (context, label) in [(2, "first"), (2, "second"), (5, "third"), (5, "fourth"), (2, "fifth")] do
    let ((billResult, dashboard), next, hit) := slot.consumePair (bill label) (monitor label) context
    unless hit == (previous == some context) && billResult.amount == context+2 &&
        billResult.capacity == context+5 && billResult.label == label &&
        dashboard == s!"{label}:{context+2}/{context+2}:{if context%2==0 then "on" else "off"}" do
      throw (IO.userError "shared views differ from independent billing/monitoring control")
    let raw := next.read context
    unless raw.2.2 && raw.1.val.2.2.1.val == context+99 && (show String from raw.1.val.2.2.2.1) == s!"private-{context}" do
      throw (IO.userError "shared read lost hidden broad data")
    let publicSlot := next.retargetView billed billedIncluded expose reveal Billing billingProof replacement compatible
    let (retained, publicNext, retainedHit) := publicSlot.consume (invoice (label++"-replacement")) context
    let (fresh, _, freshHit) := publicNext.consume (invoice "new-context") (context+1)
    unless retainedHit && !freshHit && retained.amount == context+2 &&
        retained.label == label++"-replacement" && fresh.amount == context+3 do
      throw (IO.userError "representation replacement lost public data or cache policy")
    IO.println s!"{label}: amount={billResult.amount}, dependencyHit={hit}, monitor={dashboard}, replacementHit={retainedHit}"
    slot := next
    previous := some context

end LeanPoo.Examples.SharedReporting
