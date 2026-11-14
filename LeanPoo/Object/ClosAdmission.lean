-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosAdmission

structure Signature where
  hasKey : Bool
  keys : List Nat
  allowOther : Bool

inductive Admission where
  | noApplicable | malformed | unknown | accept
  deriving DecidableEq, Repr

-- The caller supplies applicable signatures and a decoded keyword tail.
-- none represents a malformed raw tail. The control key is removed separately.
def admitCall (generic : Signature) (applicable : List Signature)
    (tail : Option (List Nat)) (allowInCall : Bool) : Admission :=
  if applicable.isEmpty then .noApplicable
  else if (generic :: applicable).any (·.hasKey) then
    match tail with
    | none => .malformed
    | some names =>
      let signatures := generic :: applicable
      if allowInCall || signatures.any (·.allowOther) ||
          names.all (fun name => signatures.any (fun s => s.keys.contains name))
      then .accept else .unknown
  else .accept

theorem empty_generic_key_checks_tail (name : Nat) :
    admitCall ⟨true, [], false⟩ [⟨false, [], false⟩] (some [name]) false = .unknown :=
  rfl

theorem empty_method_key_checks_tail (name : Nat) :
    admitCall ⟨false, [], false⟩ [⟨true, [], false⟩] (some [name]) false = .unknown :=
  rfl

theorem applicable_method_contributes_key (name : Nat) :
    admitCall ⟨true, [], false⟩ [⟨true, [name], false⟩] (some [name]) false = .accept := by
  simp [admitCall]

theorem malformed_tail_precedes_allowance (generic : Signature)
    (applicable : List Signature) (present : applicable ≠ [])
    (hasKey : (generic :: applicable).any (·.hasKey) = true) :
    admitCall generic applicable none true = .malformed := by
  cases applicable with
  | nil => contradiction
  | cons method rest => simp [admitCall, hasKey]

theorem no_applicable_precedes_keyword_checks (generic : Signature)
    (tail : Option (List Nat)) (allowInCall : Bool) :
    admitCall generic [] tail allowInCall = .noApplicable := rfl

-- A lookup returns presence independently of the value, including false.
theorem share_keyword_lookup (find : Nat → Option V) (key : Nat) (fallback : Unit → V) :
    ((find key).getD (fallback ()), (find key).isSome) =
      (let entry := find key
       (entry.getD (fallback ()), entry.isSome)) := rfl

structure Method where
  id : Nat
  signature : Nat
  deriving DecidableEq

structure GenericState where
  methods : List Method
  owner : Nat → Option Nat
  generation : Nat

def stageMethod (generic : Nat) (state : GenericState) (method : Method) : GenericState :=
  let replaced := state.methods.filter (fun old => old.signature == method.signature)
  { methods := method :: state.methods.filter (fun old => old.signature != method.signature)
    owner := fun id =>
      if id == method.id then some generic
      else if replaced.any (fun old => old.id == id) then none
      else state.owner id
    generation := state.generation + 1 }

def planBundle (generic : Nat) (admit : GenericState → Method → Except E Unit) :
    GenericState → List Method → Except E GenericState
  | state, [] => .ok state
  | state, method :: rest => do
    admit state method
    planBundle generic admit (stageMethod generic state method) rest

-- The runtime must validate the whole plan and preflight all edited owners
-- before publishing any of these fields. Publication calls no author code.
def installBundle (generic : Nat) (admit : GenericState → Method → Except E Unit)
    (writable : GenericState → Except E Unit) (before : GenericState)
    (methods : List Method) : Except E Unit × GenericState :=
  match planBundle generic admit before methods with
  | .error cause => (.error cause, before)
  | .ok after =>
    match writable after with
    | .error cause => (.error cause, before)
    | .ok () => (.ok (), after)

theorem failure_preserves_methods_owners_and_generation
    (generic : Nat) (admit : GenericState → Method → Except E Unit)
    (writable : GenericState → Except E Unit) (before : GenericState)
    (methods : List Method) (cause : E)
    (failed : (installBundle generic admit writable before methods).1 = .error cause) :
    (installBundle generic admit writable before methods).2 = before := by
  cases plan : planBundle generic admit before methods with
  | error _ => simp [installBundle, plan]
  | ok after =>
    cases ready : writable after with
    | error _ => simp [installBundle, plan, ready]
    | ok value => cases value; simp [installBundle, plan, ready] at failed

theorem successful_plan_preserves_generation_count
    (generic : Nat) (admit : GenericState → Method → Except E Unit)
    (before after : GenericState) (methods : List Method)
    (planned : planBundle generic admit before methods = .ok after) :
    after.generation = before.generation + methods.length := by
  induction methods generalizing before with
  | nil => cases planned; simp
  | cons method rest ih =>
    cases result : admit before method with
    | error _ => simp [planBundle, result, Except.bind, Bind.bind] at planned
    | ok value =>
      cases value
      have step : planBundle generic admit (stageMethod generic before method) rest =
          .ok after := by simpa [planBundle, result, Except.bind, Bind.bind] using planned
      simpa [stageMethod, Nat.add_assoc, Nat.add_comm 1 rest.length] using
        ih (stageMethod generic before method) step

example :
    let initial : GenericState := ⟨[⟨0, 0⟩], fun _ => some 0, 4⟩
    let allow (_ : GenericState) (method : Method) :=
      if method.id == 2 then Except.error 2 else .ok ()
    (installBundle 0 allow (fun _ => .ok ()) initial [⟨1, 0⟩, ⟨2, 1⟩]).2 = initial := rfl

end LeanPoo.Object.ClosAdmission

namespace LeanPoo.Object.ClosAdmission.CallValidation

inductive Descriptor where
  | generic
  | method
  deriving DecidableEq

/-- Native evidence must cover the exact descriptor, field policy, and all
    transitive dependencies. Their interpretation belongs to the runtime. -/
structure Support where
  descriptor : Descriptor
  receiver : Nat
  policy : Nat
  roots : List Nat
  payload : List Nat
  deriving DecidableEq

structure Checked where
  support : Support
  epoch : Nat
  deriving DecidableEq

inductive Boundary where
  | closed
  | observer
  | author
  | replacement
  | publicEntry
  deriving DecidableEq

def canReplay (boundary : Boundary) (epoch : Nat) (current : Support)
    (issued : Checked) : Bool :=
  decide (boundary = .closed ∧ issued.epoch = epoch ∧ issued.support = current)

theorem replay_requires_exact_support {boundary epoch current issued}
    (h : canReplay boundary epoch current issued = true) :
    boundary = .closed ∧ issued.epoch = epoch ∧ issued.support = current := by
  simpa [canReplay] using h

/-- Replaying is equivalent only with a current native witness and the intact
    original delivery order. The hypothesis is a Scheme proof obligation,
    not a claim that descriptor identity alone proves currentness. -/
theorem reuse_preserves_success_and_delivery
    (check : Support → Bool) (boundary : Boundary) (epoch : Nat)
    (current : Support) (issued : Checked)
    (admitted : check issued.support = true)
    (reuse : canReplay boundary epoch current issued = true) :
    (true, issued.support.roots) = (check current, current.roots) := by
  obtain ⟨_, _, same⟩ := replay_requires_exact_support reuse
  rw [← same, admitted]

theorem effect_boundary_requires_check (boundary : Boundary) (epoch : Nat)
    (current : Support) (issued : Checked) (effect : boundary ≠ .closed) :
    canReplay boundary epoch current issued = false := by
  simp [canReplay, effect]

theorem change_requires_check (epoch : Nat) (current : Support) (issued : Checked)
    (changed : issued.support ≠ current) :
    canReplay .closed epoch current issued = false := by
  simp [canReplay, changed]

/-- Earlier failures still win, even when the later nested descriptor can be
    reused. A miss invokes the ordinary validator at its original position. -/
def validateField (earlier nested later : Bool) : Nat :=
  if !earlier then 1 else if !nested then 2 else if !later then 3 else 0

theorem reuse_preserves_first_failure (earlier later : Bool)
    (check : Support → Bool) (epoch : Nat) (current : Support) (issued : Checked)
    (admitted : check issued.support = true)
    (reuse : canReplay .closed epoch current issued = true) :
    validateField earlier true later = validateField earlier (check current) later := by
  obtain ⟨_, _, same⟩ := replay_requires_exact_support reuse
  rw [← same, admitted]


theorem replay_after_epoch_change_refused (current : Support) (issued : Checked) :
    canReplay .closed (issued.epoch + 1) current issued = false := by
  simp [canReplay]

theorem receiver_identity_is_insufficient (issued : Checked) (current : Support)
    (differentPolicy : issued.support.policy ≠ current.policy) :
    canReplay .closed issued.epoch current issued = false := by
  apply change_requires_check
  intro same
  exact differentPolicy (congrArg Support.policy same)

theorem generic_evidence_cannot_certify_method (issued : Checked) (current : Support)
    (generic : issued.support.descriptor = .generic)
    (method : current.descriptor = .method) :
    canReplay .closed issued.epoch current issued = false := by
  apply change_requires_check
  intro same
  have equality := congrArg Support.descriptor same
  rw [generic, method] at equality
  contradiction


/-- A Slot can retain the same list identity and issuance while a pair's
    contents change. The membership predicate sees the contents. -/
structure MutableMethodSpine where
  slotIdentity : Nat
  qualifiers : List Nat

def BuiltinMethodSpineValid (spine : MutableMethodSpine) : Bool :=
  spine.qualifiers.all (· < 4)

theorem slot_identity_does_not_prove_method_spine :
    ∃ previous current : MutableMethodSpine,
      previous.slotIdentity = current.slotIdentity ∧
      BuiltinMethodSpineValid previous = true ∧
      BuiltinMethodSpineValid current = false := by
  exact ⟨⟨1, [0, 1]⟩, ⟨1, [0, 4]⟩, rfl, rfl, rfl⟩

/-- The fast interval never inherits approval from an earlier call. -/
inductive CheckStep where
  | admit (checked : Checked)
  | boundary
  | finish

def activeSupport (steps : List CheckStep) : Option Checked :=
  steps.foldl (fun _ step => match step with
    | .admit checked => some checked
    | .boundary | .finish => none) none

theorem support_revoked_at_boundary (steps : List CheckStep) :
    activeSupport (steps ++ [.boundary]) = none := by
  simp [activeSupport, List.foldl_append]

theorem support_does_not_escape_call (steps : List CheckStep) :
    activeSupport (steps ++ [.finish]) = none := by
  simp [activeSupport, List.foldl_append]


/-- Proof of the first-failure rule when the optimized path can decline. -/
def checkOrReuse (boundary : Boundary) (epoch : Nat) (current : Support)
    (issued : Checked) (ordinary : Support → Bool) : Bool :=
  if canReplay boundary epoch current issued then true else ordinary current

theorem checkOrReuse_eq (boundary : Boundary) (epoch : Nat)
    (current : Support) (issued : Checked) (ordinary : Support → Bool)
    (admitted : ordinary issued.support = true) :
    checkOrReuse boundary epoch current issued ordinary = ordinary current := by
  unfold checkOrReuse
  split
  · rename_i reuse
    obtain ⟨_, _, same⟩ := replay_requires_exact_support reuse
    rw [← same, admitted]
  · rfl

theorem pair_payload_is_part_of_support (issued : Checked) (current : Support)
    (changed : issued.support.payload ≠ current.payload) :
    canReplay .closed issued.epoch current issued = false := by
  apply change_requires_check
  intro same
  exact changed (congrArg Support.payload same)

end LeanPoo.Object.ClosAdmission.CallValidation
