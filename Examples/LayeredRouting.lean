import LeanPoo.Functional.OrderedDictionary
import LeanPoo.Functional.ContextPullback

/-! Source AVL dictionaries store first-class factories. Ordered regional
overwrites and a sparse emergency dictionary select a joint routing family;
exact-context caching shares dependencies across current request labels. -/
namespace LeanPoo.Examples.LayeredRouting
open Functional Prototype Requirements

structure Route (budget : Nat) where
  endpoint : String
  allowance : Nat
  bounded : allowance ≤ budget

def route (endpoint : String) (divisor : Nat) : Factory Nat Route :=
  fun budget => ⟨endpoint, budget / divisor, Nat.div_le_self budget divisor⟩

def primary := route "primary" 2
def regionalEarly := route "regional-old" 3
def regionalPrimary := route "regional" 4
def emergencyPrimary := route "emergency" 4
def backup := route "backup" 4
def telemetry := route "telemetry" 4

abbrev Routes := OrderedDictionary OrderOps.integer (· < ·) (Factory Nat Route)
def blank : Routes := OrderedDictionary.empty _ _ OrderOps.integer_laws
def baseEntries : List (Int × Factory Nat Route) := [(10, primary), (20, primary), (30, telemetry)]
def regionEntries : List (Int × Factory Nat Route) :=
  [(10, regionalEarly), (10, regionalPrimary), (20, backup)]
def base : Routes := blank.writeMany baseEntries
def regional : Routes := base.writeMany regionEntries
def emergency : Routes := blank.writeMany [(10, emergencyPrimary)]
def deployed : Routes := regional.merge emergency

theorem emergency_entries : emergency.tree.inorder = [(10, emergencyPrimary)] := rfl

def selected : Provider Nat Int (fun budget _ => Route budget) := fun key =>
  if key = 10 then some emergencyPrimary else if key = 20 then some backup
  else if key = 30 then some telemetry else none

/-- Every key, including undeclared keys, observes the ordered layer model. -/
theorem deployed_lookup (key : Int) : deployed.provider key = selected key := by
  have baseView : base.get = baseEntries.foldl OrderedDictionary.writeView blank.get :=
    funext (blank.get_writeMany baseEntries)
  have regionView : regional.get = regionEntries.foldl OrderedDictionary.writeView base.get :=
    funext (base.get_writeMany regionEntries)
  change (regional.merge emergency).get key = selected key
  rw [OrderedDictionary.get_merge, emergency_entries, regionView, baseView]
  by_cases first : key = 10
  · simp [baseEntries, regionEntries, OrderedDictionary.writeView, selected, first]
  · by_cases second : key = 20
    · simp [baseEntries, regionEntries, OrderedDictionary.writeView, selected, second]
    · by_cases third : key = 30
      · simp [baseEntries, regionEntries, OrderedDictionary.writeView, selected, third]
      · simp [baseEntries, regionEntries, OrderedDictionary.writeView, selected, first, second, third,
          blank, OrderedDictionary.empty, OrderedDictionary.get, Dictionary.avl, Dictionary.structural,
          Tree.search]

abbrev keys : List Int := [10, 20, 30]
def Fits (budget : Nat) (data : Results (fun budget (_ : Int) => Route budget) budget keys) : Prop :=
  data.1.allowance + data.2.1.allowance + data.2.2.1.allowance ≤ budget

theorem admit (factories : Factories Nat (fun budget (_ : Int) => Route budget) keys)
    (aligned : Selected deployed.provider keys factories) :
    ∀ budget, Fits budget (build factories budget) := by
  rcases factories with ⟨first, second, third, tail⟩
  have a : first = emergencyPrimary := by
    have := aligned.1
    rw [deployed_lookup] at this
    simpa [selected] using this.symm
  have b : second = backup := by
    have := aligned.2.1
    rw [deployed_lookup] at this
    simpa [selected] using this.symm
  have c : third = telemetry := by
    have := aligned.2.2.1
    rw [deployed_lookup] at this
    simpa [selected] using this.symm
  subst first; subst second; subst third
  intro budget
  simp only [Fits, build, emergencyPrimary, backup, telemetry, route]
  omega

structure Request where
  budget : Nat
  label : String

structure Plan (request : Request) where
  endpoints : List String
  reserved : Nat
  fits : reserved ≤ request.budget
  label : String

def construct (request : Request) (data : Results (fun budget (_ : Int) => Route budget) request.budget keys)
    (valid : Fits request.budget data) : Plan request :=
  ⟨[data.1.endpoint, data.2.1.endpoint, data.2.2.1.endpoint],
    data.1.allowance + data.2.1.allowance + data.2.2.1.allowance, valid, request.label⟩

theorem prepared : prepare deployed.provider keys = .ok (emergencyPrimary, backup, telemetry, PUnit.unit) := by
  apply (prepare_ok_iff _ _ _).mpr
  simp [Selected, deployed_lookup, selected]

theorem missing_first : prepare deployed.provider [10, 99, 20] = .error 99 := by
  simp [prepare, deployed_lookup, selected]

def scenario : Except Int (List (List String × Nat × String × Bool)) := do
  let ready ← prepareCertified deployed.provider keys Fits admit
  let mut slot := ContextSlot.empty ready
  let mut outputs := []
  for request in [Request.mk 12 "first", ⟨12, "second"⟩, ⟨8, "third"⟩, ⟨12, "fourth"⟩] do
    let (plan, next, hit) := slot.consumeAlong Request.budget construct request
    slot := next
    outputs := outputs ++ [(plan.endpoints, plan.reserved, plan.label, hit)]
  return outputs

#guard scenario.toOption == some [
  (["emergency", "backup", "telemetry"], 9, "first", false),
  (["emergency", "backup", "telemetry"], 9, "second", true),
  (["emergency", "backup", "telemetry"], 6, "third", false),
  (["emergency", "backup", "telemetry"], 9, "fourth", false)]
#eval IO.println s!"layered routes (endpoints, reserved, current label, dependency hit): {repr scenario.toOption}"

end LeanPoo.Examples.LayeredRouting
