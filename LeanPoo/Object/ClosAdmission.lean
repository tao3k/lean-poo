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

namespace LeanPoo.Object.ClosAdmission.DirectPrimary

inductive Read where
  | source (key : Nat)
  | privateCarrier (key : Nat)
  deriving DecidableEq, Repr

inductive Failure where
  | arity | applicability | keyword | effective | frame | body
  deriving DecidableEq, Repr

abbrev Phase (S A : Type) := S → Except Failure A × S × List Read

def thenRun (first : Phase S A) (next : A → Phase S B) : Phase S B :=
  fun state =>
    match first state with
    | (.error failure, after, reads) => (.error failure, after, reads)
    | (.ok value, after, reads) =>
      let (result, final, later) := next value after
      (result, final, reads ++ later)

def visible : List Read → List Read
  | [] => []
  | .source key :: rest => .source key :: visible rest
  | .privateCarrier _ :: rest => visible rest

theorem visible_append (left right : List Read) :
    visible (left ++ right) = visible left ++ visible right := by
  induction left with
  | nil => rfl
  | cons head rest ih => cases head <;> simp [visible, ih]

def observe (entry : Phase S A) (state : S) :=
  let (answer, after, reads) := entry state
  (answer, after, visible reads)

/-- The shared admission includes arity, applicability, keyword and the live
    external descriptor checks. The remaining private step must succeed,
    preserve state, and contribute only unobservable carrier reads. -/
theorem eliminate_private_carriers (admission : Phase S P)
    (carriers : P → Phase S C) (ordinaryBody : P → C → Phase S A)
    (directBody : P → Phase S A)
    (privateOnly : ∀ payload state, ∃ carrier reads,
      carriers payload state = (.ok carrier, state, reads) ∧ visible reads = [] ∧
      ordinaryBody payload carrier state = directBody payload state)
    (state : S) :
    observe (thenRun admission (fun payload => thenRun (carriers payload) (ordinaryBody payload))) state =
    observe (thenRun admission directBody) state := by
  unfold observe thenRun
  cases h : admission state with
  | mk outcome tail =>
    rcases tail with ⟨after, prior⟩
    cases outcome with
    | error failure => rfl
    | ok payload =>
      obtain ⟨carrier, reads, admitted, hidden, body⟩ := privateOnly payload after
      simp [admitted, hidden, body, visible_append]

inductive Route where
  | closedPrimary | openObserver | openCallback | replacement | publicCarrier | nextMethod
  deriving DecidableEq

def invoke (route : Route) (qualified : Bool) (ordinary direct : Phase S A) : Phase S A :=
  if route = .closedPrimary ∧ qualified then direct else ordinary

theorem effect_or_escape_uses_ordinary (route : Route) (qualified : Bool)
    (ordinary direct : Phase S A) (outside : route ≠ .closedPrimary) :
    invoke route qualified ordinary direct = ordinary := by
  simp [invoke, outside]

/-- An arbitrary observer can inspect the carrier read itself. Such a trace
    cannot use the projection in eliminate_private_carriers. -/
theorem raw_carrier_delivery_is_observable :
    ([Read.privateCarrier 0] : List Read) ≠ [] := by decide


/-- A direct entry cannot use the theorem when the omitted step would refuse.
    Running the actual admission sequence is necessary even for one method. -/
theorem failing_carrier_cannot_be_erased :
    let admission : Phase Unit Unit := fun s => (.ok (), s, [])
    let carrier : Unit → Phase Unit Unit := fun _ s => (.error .frame, s, [])
    let body : Unit → Phase Unit Unit := fun _ s => (.ok (), s, [])
    observe (thenRun admission (fun value => thenRun (carrier value) fun _ => body value)) () ≠
      observe (thenRun admission body) () := by
  dsimp [observe, thenRun]
  intro same
  cases same

end LeanPoo.Object.ClosAdmission.DirectPrimary

namespace LeanPoo.Object.ClosAdmission.DirectPrimary

/-- A carrier allocation can be deferred for a lexical entry that cannot
    refer to the frame. The failure from a body keeps the same position. -/
theorem frame_free_body_preserves_failure {S A : Type}
    (body : Phase S A) (state : S) (carrier : Nat) :
    observe
      (thenRun (fun current => (.ok carrier, current, [.privateCarrier 0]))
        (fun _ => body)) state = observe body state := by
  simp [observe, thenRun, visible]

/-- A snapshot of the full external trace is not required by this
    transformation. The external admission itself is performed in both. -/
example (admission : Phase Unit Unit) (body : Phase Unit Unit) :
    observe
      (thenRun admission (fun _ =>
        thenRun (fun current => (.ok (), current, [.privateCarrier 0]))
          (fun _ => body))) () =
    observe (thenRun admission (fun _ => body)) () := by
  apply eliminate_private_carriers
  intro _ state
  exact ⟨(), [.privateCarrier 0], rfl, rfl, rfl⟩

end LeanPoo.Object.ClosAdmission.DirectPrimary

namespace LeanPoo.Object.ClosAdmission.IndexedRank

variable {K M R S E : Type}

/-- A prepared index replaces only a pure identity-position lookup. Slot
    demand and the independent applicability steps remain in the same order. -/
theorem indexed_rank_preserves_scan
    (slow fast : K → Option Nat) (same : ∀ key, fast key = slow key)
    (scan : (K → Option Nat) → List M → S → Except E (List R) × S)
    (methods : List M) (state : S) :
    scan fast methods state = scan slow methods state := by
  rw [show fast = slow from funext same]

/-- A previously prepared row is legal only for the identical live roster.
    A changed roster or epoch recomputes through the current order. -/
def selectRoster [DecidableEq M] (oldEpoch liveEpoch : Nat)
    (previous current : List M) : List M :=
  if oldEpoch = liveEpoch ∧ previous = current then previous else current

theorem replacement_keeps_current_roster [DecidableEq M] (oldEpoch liveEpoch : Nat)
    (previous current : List M) :
    selectRoster oldEpoch liveEpoch previous current = current := by
  unfold selectRoster
  split
  · rename_i h
    exact h.2
  · rfl

/-- The selected bucket is a stable restriction of the roster, with positions
    preserved even when candidate keys collide. -/
theorem indexed_bucket_positions (roster : List M) (select : M → Bool) :
    ∀ start, ((roster.zipIdx start).filter (fun row => select row.1)).map Prod.fst =
      roster.filter select := by
  induction roster with
  | nil => intro start; rfl
  | cons head tail ih =>
    intro start
    cases h : select head <;> simp [List.zipIdx_cons, h, ih]

end LeanPoo.Object.ClosAdmission.IndexedRank

namespace LeanPoo.Object.ClosAdmission.IndexedRank

def position [DecidableEq K] (key : K) : List K → Option Nat
  | [] => none
  | head :: tail => if head = key then some 0 else (position key tail).map (· + 1)

/-- Supported POO invalidations discard the canonical spine. A row can
    accelerate lookup only while its recorded spine is the current one. -/
theorem live_spine_rank [DecidableEq K] (key : K) (current installed : List K)
    (sameOwner : Bool) (indexed : K → Option Nat)
    (correct : ∀ k, indexed k = position k installed) :
    (if sameOwner && decide (installed = current) then indexed key else position key current) =
      position key current := by
  split
  · rename_i h
    have same : installed = current := by simpa using (Bool.and_eq_true_iff.mp h).2
    simpa [same] using correct key
  · rfl

end LeanPoo.Object.ClosAdmission.IndexedRank

namespace LeanPoo.Object.ClosAdmission.IndexedRank

private def reverseOwners [DecidableEq K] (source : K) (rows : List (M × List K)) :=
  rows.filter fun row => row.2.contains source

theorem unrelated_row_survives_invalidation [DecidableEq K] (source : K)
    (rows : List (M × List K)) (row : M × List K)
    (member : row ∈ rows) (unrelated : source ∉ row.2) :
    row ∈ (rows.filter fun entry => !(entry.2.contains source)) := by
  simp [member, unrelated]

theorem affected_row_is_in_reverse_bucket [DecidableEq K] (source : K)
    (rows : List (M × List K)) (row : M × List K)
    (member : row ∈ rows) (affected : source ∈ row.2) :
    row ∈ reverseOwners source rows := by
  simp [reverseOwners, member, affected]

end LeanPoo.Object.ClosAdmission.IndexedRank

namespace LeanPoo.Object.ClosAdmission.IndexedRank

variable {M R S E O : Type}

abbrev Attempt (S E O R : Type) := S → Except E (Option R) × S × List O

def scan (evaluate : M → Attempt S E O R) :
    List M → S → Except E (List R) × S × List O
  | [], state => (.ok [], state, [])
  | row :: rest, state =>
    match evaluate row state with
    | (.error refusal, after, reads) => (.error refusal, after, reads)
    | (.ok result, after, reads) =>
      let (later, final, more) := scan evaluate rest after
      (later.map (fun accepted => result.toList ++ accepted), final, reads ++ more)

/-- A bucket may remove only proven misses with no observable delivery or
    state change. Equality includes the first refusal and the prefix of
    reads delivered before it. -/
theorem prune_closed_misses (evaluate : M → Attempt S E O R)
    (keep : M → Bool) (rows : List M)
    (skippable : ∀ row, keep row = false → ∀ state,
      evaluate row state = (.ok none, state, [])) (state : S) :
    scan evaluate (rows.filter keep) state = scan evaluate rows state := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
    cases kept : keep row with
    | false =>
      simp [kept, scan, skippable row kept state, ih]
      cases h : scan evaluate rest state with
      | mk result tail => cases result <;> rfl
    | true =>
      simp only [List.filter_cons, kept, ite_true, scan]
      cases h : evaluate row state with
      | mk result tail =>
        rcases tail with ⟨after, reads⟩
        cases result <;> simp only [ih]

/-- A Scheme pair write may change a row without advancing the Generic's
    epoch. Both a new match and an effectful refusal are possible. -/
theorem mutable_roster_epoch_insufficient :
    let row : Attempt Bool Nat Nat Nat := fun changed =>
      if changed then (.error 17, changed, [42]) else (.ok none, changed, [])
    scan (fun _ : Unit => row) [] true ≠ scan (fun _ : Unit => row) [()] true := by
  dsimp [scan]
  intro same
  cases same

/-- For a slotted projection of the ranked sequence, two candidates assigned
    the same position must be the same owner. Filling a position only once
    therefore gives the same first-match result as a linear lookup. -/
theorem first_position_lookup [DecidableEq M] [DecidableEq K]
    (position : M → K) (owner : R → M)
    (unique : Function.Injective position) (ranked : List R) (method : M) :
    ranked.find? (fun row => position (owner row) == position method) =
      ranked.find? (fun row => owner row == method) := by
  congr 1
  funext row
  by_cases same : owner row = method
  · simp [same]
  · have different : position (owner row) ≠ position method :=
      fun h => same (unique h)
    have left : (position (owner row) == position method) = false := beq_eq_false_iff_ne.mpr different
    have right : (owner row == method) = false := beq_eq_false_iff_ne.mpr same
    rw [left, right]

end LeanPoo.Object.ClosAdmission.IndexedRank

namespace LeanPoo.Object.ClosAdmission.IndexedRank

/-- A publication position is only a hint for a live rank. Even an arbitrary
    stale position cannot inject a row or change which duplicate wins. -/
theorem checked_position_falls_back [DecidableEq M]
    (owner : R → M) (ranked : List R) (method : M)
    (hint : Option R)
    (validHint : ∀ row, hint = some row → owner row = method →
      ranked.find? (fun entry => owner entry == method) = some row) :
    (match hint with
     | some row =>
       if owner row = method then some row else ranked.find? (fun entry => owner entry == method)
     | none => ranked.find? (fun entry => owner entry == method)) =
      ranked.find? (fun entry => owner entry == method) := by
  cases hint with
  | none => rfl
  | some row =>
    by_cases same : owner row = method
    · simp [same, validHint row rfl same]
    · simp [same]

end LeanPoo.Object.ClosAdmission.IndexedRank

namespace LeanPoo.Object.ClosAdmission.OwnedMethods

abbrev Method := Nat
abbrev Specializer := Nat

structure Row where
  method : Method
  specializers : List Specializer
  deriving DecidableEq

structure Publication where
  generation : Nat
  rows : List Row
  deriving DecidableEq

structure Reflection where
  methods : List Method
  specializers : List (List Specializer)

def reflect (publication : Publication) : Reflection :=
  ⟨publication.rows.map (·.method), publication.rows.map (·.specializers)⟩

/-- Reflection gives the caller a fresh spine at each level. Scheme preserves
    the identities in the spines. A pair write addresses only the reflection. -/
def editReflection (publication : Publication) (edit : Reflection → Reflection) :
    Publication × Reflection :=
  (publication, edit (reflect publication))

theorem reflection_edit_preserves_published_inputs
    (publication : Publication) (edit : Reflection → Reflection) :
    (editReflection publication edit).1 = publication := rfl

/-- A reflected spine consists of newly allocated cells. The writer edits
    only those addresses. Car values may still be shared descriptor identities. -/
def writeCell (heap : Nat → V) (address : Nat) (value : V) : Nat → V :=
  fun key => if key = address then value else heap key

theorem reflected_cell_write_preserves_owned_cells (heap : Nat → V)
    (owned reflected : List Nat) (disjoint : ∀ a ∈ reflected, a ∉ owned)
    (address : Nat) (member : address ∈ reflected) (value : V) :
    owned.map (writeCell heap address value) = owned.map heap := by
  apply List.map_congr_left
  intro key inOwned
  have separate : key ≠ address := by
    intro same
    exact disjoint address member (same ▸ inOwned)
  simp [writeCell, separate]

def replace (publication : Publication) (method : Method)
    (specializers : List Specializer) : Publication :=
  ⟨publication.generation + 1, publication.rows.map fun row =>
    if row.method = method then { row with specializers } else row⟩

theorem replacement_preserves_unrelated_rows
    (publication : Publication) (method : Method) (specializers : List Specializer)
    (row : Row) (member : row ∈ publication.rows) (unrelated : row.method ≠ method) :
    row ∈ (replace publication method specializers).rows := by
  apply List.mem_map.mpr
  exact ⟨row, member, by simp [unrelated]⟩

/-- The reverse index transposes the dependencies used to certify a row. A
    source edit revokes exactly its registered rows. A clean row's witnesses
    can therefore still certify applicability for the same arguments. -/
def reverseBucket (source : Specializer) (publication : Publication) : List Row :=
  publication.rows.filter fun row => row.specializers.contains source

theorem dirty_row_iff_registered (source : Specializer) (publication : Publication) (row : Row) :
    row ∈ reverseBucket source publication ↔
      row ∈ publication.rows ∧ source ∈ row.specializers := by
  simp [reverseBucket]

theorem unaffected_row_matches_after_edit (source : Specializer)
    (before after : Specializer → Bool) (row : Row)
    (unchanged : ∀ key, key ≠ source → before key = after key)
    (unaffected : source ∉ row.specializers) :
    row.specializers.all before = row.specializers.all after := by

  obtain ⟨id, keys⟩ := row
  change source ∉ keys at unaffected
  change keys.all before = keys.all after
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    have absent : key ≠ source := fun same => unaffected (by simp [same])
    have tail : source ∉ rest := fun mem => unaffected (List.mem_cons_of_mem _ mem)
    simp [unchanged key absent, ih tail]

end LeanPoo.Object.ClosAdmission.OwnedMethods
