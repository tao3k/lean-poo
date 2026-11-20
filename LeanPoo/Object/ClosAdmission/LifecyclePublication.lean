-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission
import LeanPoo.Object.ClosAdmission.ClassDispatchDependencies

namespace LeanPoo.Object.ClosAdmission.LifecyclePublication
open PublishedDispatch
open ClassDispatchDependencies
open LeanPoo.Functional.StrongComponents (Reach)
open LeanPoo.Functional.LocalSccRegion (Edge)

/-- The recipe holds the ordered roots of one actual Generic admission.
Its support is the transitive set of inputs to that admission. Root identities
are scoped to the receiver that issued them and its committed generation. -/
structure Admission (Root : Type) where
  receiver : Nat
  generation : Nat
  roots : List Root

abbrev Check (n : Nat) (Value Runtime Root Event Failure : Type) :=
  Stage n Value Runtime (Option (Admission Root)) Event Failure

/-- The native sweep must run only for a closed route. It checks the saved
roots without delivering reads or calling author code. An open route never
installs a collector, even if a publication for its Generic is current.
The route itself must be resolved by quiet checks before opening a scope. -/
def qualify (route : DirectPrimary.Route) (receiver generation : Nat)
    (stage : Check n Value Runtime Root Event Failure) (world : World n Value Runtime)
    (entry : Published n (Option (Admission Root))) (authenticate : List Root → Bool) :
    Option (Admission Root) := do
  letI : Decidable (current stage world entry) :=
    inferInstanceAs (Decidable (entry.owner = stage.owner ∧ entry.epoch = world.epoch stage.owner))
  if route = .closedPrimary ∧ current stage world entry then do
    let admission ← entry.plan
    if admission.receiver = receiver ∧ admission.generation = generation then
      if authenticate admission.roots then some admission else none
    else none
  else none

/-- A hit supplies the whole successful cold result, including its order.
Registration must include all changes relevant to the descriptor checks:
receiver fields, method roster, nested validators (including the live
ClosClass predicate), and their transitive slot reads. Runtime arguments
and effectful checks are not inputs to this pure publication. -/
theorem qualified_eq_cold {union : Edge n} {dirty : Fin n → Prop}
    (stage : Check n Value Runtime Root Event Failure) (before after : World n Value Runtime)
    (entry : Published n (Option (Admission Root)))
    (route receiver generation authenticate) (admission : Admission Root)
    (past : entry.epoch ≤ before.epoch stage.owner)
    (issued : current stage before entry → entry.plan = cold stage before)
    (registered : ∀ source ∈ stage.support, Reach union source stage.owner)
    (inputs : ∀ source, ¬ dirty source → after.input source = before.input source)
    (advanced : after.epoch = advanceEpoch union dirty before.epoch)
    (hit : qualify route receiver generation stage after entry authenticate = some admission) :
    cold stage after = some admission := by
  by_cases eligible : route = .closedPrimary ∧ current stage after entry
  · have same : entry.plan = cold stage after :=
      prior_entry_valid_after_edit stage before after entry past issued registered inputs advanced eligible.2
    cases plan : entry.plan with
    | none => simp [qualify, eligible, plan] at hit
    | some saved =>
      by_cases identity : saved.receiver = receiver ∧ saved.generation = generation
      · by_cases authentic : authenticate saved.roots = true
        · have eq : saved = admission := by simpa [qualify, eligible, plan, identity, authentic] using hit
          exact same.symm.trans (plan.trans (congrArg some eq))
        · simp [qualify, eligible, plan, identity, authentic] at hit
      · simp [qualify, eligible, plan, identity] at hit
  · simp [qualify, eligible] at hit

/-- The outer and inner Generic have different owners. The second lookup
must take place in the world returned by the first; the outer receipt
cannot be offered even when both owners have the same epoch. -/
theorem other_dispatch_refused
    (outer inner : Check n Value Runtime Root Event Failure)
    (world : World n Value Runtime) (entry : Published n (Option (Admission Root)))
    (outerOwner : entry.owner = outer.owner) (distinct : outer.owner ≠ inner.owner)
    (route receiver generation authenticate) :
    qualify route receiver generation inner world entry authenticate = none := by
  simp [qualify, current, outerOwner, distinct]

/-- A receipt gathered ahead of the roster edit binds the old generation.
Copying the candidate to another object also cannot produce final roots. -/
theorem wrong_receiver_or_generation_refused
    (stage : Check n Value Runtime Root Event Failure) (world : World n Value Runtime)
    (entry : Published n (Option (Admission Root))) (saved : Admission Root)
    (plan : entry.plan = some saved) (route receiver generation authenticate)
    (wrong : saved.receiver ≠ receiver ∨ saved.generation ≠ generation) :
    qualify route receiver generation stage world entry authenticate = none := by
  have mismatch : ¬ (saved.receiver = receiver ∧ saved.generation = generation) :=
    fun ⟨r, g⟩ => wrong.elim (fun h => h r) (fun h => h g)
  simp [qualify, plan, mismatch]

/-- A direct subclass roster change in a Class read by the predicate invalidates admission.
C4 ordering still retains its epoch if none of the opened paths reach it.
The two owners use the existing ordinary and filtered reverse edges. -/
theorem class_roster_separates_admission_from_c4 {n : Nat}
    (index : ClassDispatchDependencies.Dependencies n) (classOwner admission order : Fin n)
    (readsRoster : index.ordinary classOwner admission = true) (distinct : order ≠ classOwner)
    (noRoute : ∀ next, Reach (index.opens .whole) next order →
      index.ordinary classOwner next = false) :
    Propagated index .roster classOwner admission ∧
      ¬ (order = classOwner ∨ Propagated index .roster classOwner order) :=
  ⟨.first readsRoster, roster_preserves_plan_epoch index classOwner order distinct noRoute⟩

/-- If an author replaces a validator or changes any of its dependencies,
a previously admitted receipt misses when checked in the returned world.
The same argument applies separately to each Generic owner. -/
theorem dependency_edit_refuses_after_callback
    (index : Edge n) (dirty : Fin n → Prop)
    (stage : Check n Value Runtime Root Event Failure)
    (before after : World n Value Runtime) (entry : Published n (Option (Admission Root)))
    (prior : current stage before entry) (source : Fin n)
    (registered : Reach index source stage.owner) (changed : dirty source)
    (advanced : after.epoch = advanceEpoch index dirty before.epoch)
    (route receiver generation authenticate) :
    qualify route receiver generation stage after entry authenticate = none := by
  have stale : ¬ current stage after entry := by
    intro hit
    have bumped := affected_cannot_keep_epoch index dirty before.epoch stage.owner
      ⟨source, changed, registered⟩
    exact bumped ((congrFun advanced stage.owner).symm.trans (hit.2.symm.trans prior.2))
  simp [qualify, stale]

open DirectPrimary (Phase Route thenRun observe visible)

def invoke (receipt : Option (Admission Root)) (ordinary : Phase S A)
    (direct : Admission Root → Phase S A) : Phase S A :=
  match receipt with
  | none => ordinary
  | some admitted => direct admitted

/-- No speculative execution on a miss, including an open observer or
author protocol. The ordinary path retains the entire raw trace. -/
theorem open_route_keeps_original_trace
    (stage : Check n Value Runtime Root Event Failure) (world : World n Value Runtime)
    (entry : Published n (Option (Admission Root))) (route receiver generation authenticate)
    (outside : route ≠ .closedPrimary) (ordinary : Phase S A)
    (direct : Admission Root → Phase S A) :
    invoke (qualify route receiver generation stage world entry authenticate) ordinary direct =
      ordinary := by
  simp [qualify, outside, invoke]

/-- Use after native qualification, with the same live admission and
callback continuation in both arms. A lexically frame-free method can
elide only the successful quiet EffectiveMethod/InvocationFrame step.
Any post-callback guards belong to the shared continuation. -/
theorem qualified_default_keeps_effects
    (admission : Phase S P) (carriers : P → Phase S C)
    (withFrame : P → C → Phase S A) (withoutFrame : P → Phase S A)
    (privateOnly : ∀ payload state, ∃ carrier reads,
      carriers payload state = (.ok carrier, state, reads) ∧ visible reads = [] ∧
      withFrame payload carrier state = withoutFrame payload state)
    (state : S) :
    observe (thenRun admission (fun payload => thenRun (carriers payload) (withFrame payload))) state =
      observe (thenRun admission withoutFrame) state :=
  DirectPrimary.eliminate_private_carriers admission carriers withFrame withoutFrame privateOnly state

/-- Each lookup runs at its own call site. This congruence compares the
post-effect state as well as the trace, so an inner lookup cannot run
against the outer call's pre-effect state. -/
private theorem thenRun_observe_congr
    (first first' : Phase S P) (next next' : P → Phase S A)
    (sameFirst : ∀ state, observe first state = observe first' state)
    (sameNext : ∀ payload state, observe (next payload) state = observe (next' payload) state)
    (state : S) :
    observe (thenRun first next) state = observe (thenRun first' next') state := by
  generalize h : first state = firstResult
  rcases firstResult with ⟨result, after, reads⟩
  generalize h' : first' state = firstResult'
  rcases firstResult' with ⟨result', after', reads'⟩
  have firstEq := sameFirst state
  simp only [observe, h, h', Prod.mk.injEq] at firstEq
  obtain ⟨rfl, rfl, readsEq⟩ := firstEq
  cases result with
  | error failure => simp [observe, thenRun, h, h', readsEq]
  | ok payload =>
    generalize hn : next payload after = nextResult
    rcases nextResult with ⟨answer, final, later⟩
    generalize hn' : next' payload after = nextResult'
    rcases nextResult' with ⟨answer', final', later'⟩
    have nextEq := sameNext payload after
    simp only [observe, hn, hn', Prod.mk.injEq] at nextEq
    obtain ⟨rfl, rfl, laterEq⟩ := nextEq
    simp [observe, thenRun, h, h', hn, hn', DirectPrimary.visible_append, readsEq, laterEq]

/-- Neither dispatch can reuse a successful branch for the other. Each
selector acts on its call's state and each local comparison includes
the original continuation (including any independent rechecks). -/
theorem nested_defaults_preserve_observation
    (outer : Phase S P) (inner : P → Phase S A)
    (outerQualification : S → Option (Admission Root))
    (innerQualification : P → S → Option (Admission Root))
    (outerDirect : Admission Root → Phase S P)
    (innerDirect : P → Admission Root → Phase S A)
    (outerProof : ∀ state saved, outerQualification state = some saved →
      observe (outerDirect saved) state = observe outer state)
    (innerProof : ∀ payload state saved, innerQualification payload state = some saved →
      observe (innerDirect payload saved) state = observe (inner payload) state)
    (state : S) :
    observe (thenRun
      (fun st => invoke (outerQualification st) outer outerDirect st)
      (fun payload st => invoke (innerQualification payload st) (inner payload) (innerDirect payload) st))
      state = observe (thenRun outer inner) state := by
  apply thenRun_observe_congr
  · intro st
    change (let (answer, after, reads) := invoke (outerQualification st) outer outerDirect st
            (answer, after, visible reads)) = observe outer st
    cases h : outerQualification st with
    | none => rfl
    | some saved => exact outerProof st saved h
  · intro payload st
    change (let (answer, after, reads) :=
              invoke (innerQualification payload st) (inner payload) (innerDirect payload) st
            (answer, after, visible reads)) = observe (inner payload) st
    cases h : innerQualification payload st with
    | none => rfl
    | some saved => exact innerProof payload st saved h

end LeanPoo.Object.ClosAdmission.LifecyclePublication
