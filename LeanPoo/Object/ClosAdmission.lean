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
