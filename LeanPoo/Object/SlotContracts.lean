-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.SlotContracts

-- State includes observations and effects. Failure keeps the resulting state.
abbrev Action (S E A : Type) := S → Except E A × S

def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error err, after) => (.error err, after)
    | (.ok value, after) => next value after

def pureAction (value : A) : Action S E A :=
  fun state => (.ok value, state)

-- Ordinary Slot checking keeps presence, demand, then the value predicate.
-- Presence and demand may observe reads or dispatch the receiver's protocol.
def slot (present : K → Action S E Bool) (demand : K → Action S E V)
    (name : K) (check : V → Action S E Bool) : Action S E Bool :=
  bind (present name) fun found =>
    if found then bind (demand name) check else pureAction false

def chain (first rest : Action S E Bool) : Action S E Bool :=
  bind first fun passed => if passed then rest else pureAction false

def parallelLists (test : K → P → Action S E Bool) :
    List K → List P → Action S E Bool
  | name :: names, check :: checks =>
    chain (test name check) (parallelLists test names checks)
  | _, _ => pureAction true

def declaredFields (test : K → P → Action S E Bool) :
    List (K × P) → Action S E Bool
  | [] => pureAction true
  | (name, check) :: rest => chain (test name check) (declaredFields test rest)

theorem declarations_preserve_outcome_and_effects (test : K → P → Action S E Bool)
    (fields : List (K × P)) :
    declaredFields test fields =
      parallelLists test (fields.map Prod.fst) (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨name, check⟩
    simp only [declaredFields, List.map_cons, parallelLists, ih]

theorem failed_field_skips_rest (first rest : Action S E Bool) (before after : S)
    (failed : first before = (.ok false, after)) :
    chain first rest before = (.ok false, after) := by
  simp [chain, bind, pureAction, failed]

theorem absent_slot_preserves_presence_effect (present : K → Action S E Bool)
    (demand : K → Action S E V) (name : K) (check : V → Action S E Bool)
    (before after : S) (absent : present name before = (.ok false, after)) :
    slot present demand name check before = (.ok false, after) := by
  simp [slot, bind, pureAction, absent]

-- A live prepared positive lookup uses the same method table as ordinary
-- presence. Absence still enters reflection, which may delegate to a hook.
-- No result or permission is kept across a predicate or caller callback.
structure PresenceRoute where
  prepared : Bool
  standardLookup : Bool
  observed : Bool
  localSlot : Bool

def directPresence (route : PresenceRoute) : Bool :=
  route.prepared && route.standardLookup && !route.observed && route.localSlot

def checkPresence (route : PresenceRoute) (ordinary : Action S E Bool) : Action S E Bool :=
  if directPresence route then pureAction true else ordinary

theorem direct_presence_preserves_outcome_and_effects (route : PresenceRoute)
    (ordinary : Action S E Bool)
    (positive : directPresence route = true → ordinary = pureAction true) :
    checkPresence route ordinary = ordinary := by
  unfold checkPresence
  split
  · rename_i hit
    exact (positive hit).symm
  · rfl

theorem observed_presence_keeps_all_checks (route : PresenceRoute) (ordinary : Action S E Bool) :
    checkPresence { route with observed := true } ordinary = ordinary := by
  simp [checkPresence, directPresence]

theorem missing_local_slot_can_delegate (route : PresenceRoute) (ordinary : Action S E Bool) :
    checkPresence { route with localSlot := false } ordinary = ordinary := by
  simp [checkPresence, directPresence]

theorem route_rechecked_after_callback (route : PresenceRoute) (ordinary : Action S E Bool)
    (changed : PresenceRoute) (invalid : directPresence changed = false) :
    (checkPresence route ordinary, checkPresence changed ordinary).2 = ordinary := by
  simp [checkPresence, invalid]

-- Structural capture runs the precheck before selecting the live query.
-- The fast query is limited to a prepared local hit on the standard index.
-- Signing and delivery still run, including every observer callback.
def capturePresence (before : Action S E Unit) (query : Action S E (Bool × List R))
    (finish : (Bool × List R) → Action S E A) : Action S E A :=
  bind before fun _ => bind query finish

def capturePreparedPresence (before : Action S E Unit) (localHit : S → Bool)
    (query : Action S E (Bool × List R))
    (finish : (Bool × List R) → Action S E A) : Action S E A :=
  bind before fun _ state =>
    if localHit state then finish (true, []) state
    else bind query finish state

theorem capture_prepared_presence_exact (before : Action S E Unit) (localHit : S → Bool)
    (query : Action S E (Bool × List R)) (finish : (Bool × List R) → Action S E A)
    (positive : ∀ state, localHit state = true → query state = (.ok (true, []), state)) :
    capturePreparedPresence before localHit query finish = capturePresence before query finish := by
  funext state
  unfold capturePreparedPresence capturePresence bind
  cases before state with
  | mk result after =>
    cases result with
    | error cause => rfl
    | ok _ =>
      by_cases hit : localHit after = true
      · simp [hit, positive after hit]
      · simp [hit]

-- A recorder keeps the original occurrence before observer delivery. Filtering
-- the runtime's no-op removes no delivery effects, including on failure.
def deliver (run : Observer → Action S E Unit) : List Observer → Action S E Unit
  | [] => pureAction ()
  | observer :: rest => bind (run observer) (fun _ => deliver run rest)

theorem drop_noop_observers (run : Observer → Action S E Unit)
    (noop : Observer → Bool) (observers : List Observer)
    (pure : ∀ observer, noop observer = true → run observer = pureAction ()) :
    deliver run (observers.filter (fun observer => !noop observer)) = deliver run observers := by
  induction observers with
  | nil => rfl
  | cons observer rest ih =>
    cases hit : noop observer
    · simp [hit, deliver, ih]
    · simp [hit, deliver, ih, pure observer hit]
      rfl

-- Both delivery routes run with observation disabled. Restore the enclosing
-- scope on either result while retaining the callback's effects on other state.
def withoutRecording (action : Action (Bool × S) E Unit) : Action (Bool × S) E Unit :=
  fun (active, state) =>
    let (result, (_, after)) := action (false, state)
    (result, (active, after))

theorem singleton_observer_delivery (run : Observer → Action (Bool × S) E Unit)
    (observer : Observer) :
    withoutRecording (deliver run [observer]) = withoutRecording (run observer) := by
  funext before
  rcases before with ⟨active, state⟩
  unfold withoutRecording
  simp only [deliver, bind]
  cases run observer (false, state) with
  | mk result after =>
    cases result with
    | error _ => rfl
    | ok _ => rfl

-- Slot contributions are stored most-specific first. A singleton can skip
-- reverse/fold without changing which inherited continuation it receives.
def compileContributions (applySpec : F → Spec → F) (inherited : Spec → F)
    (head : Spec) (tail : List Spec) : F :=
  let ordered := (head :: tail).reverse
  ordered.foldl applySpec (inherited (ordered.headD head))

theorem singleton_slot_contribution (applySpec : F → Spec → F) (inherited : Spec → F)
    (spec : Spec) :
    compileContributions applySpec inherited spec [] = applySpec (inherited spec) spec := rfl

-- Boolean membership consumes the private C4 order within the operation.
-- A public snapshot needs a detached spine, but membership exposes no suffix.
theorem ancestry_membership_snapshot [DecidableEq Owner] (owner : Owner)
    (order : List Owner) :
    (order.map id).contains owner = order.contains owner := by
  simp

-- A declared name is a symbol before either read begins. Symbol admission
-- depends only on that name, so the same fact can be used after an observer.
-- Receiver admission, demand, delivery, and the child contract remain actions
-- on the state produced by the preceding operation.
def admitName (valid : K → Bool) (cause : E) (name : K) : Action S E Unit :=
  fun state => (if valid name then .ok () else .error cause, state)

theorem reuse_declared_slot_name (valid : K → Bool) (cause : E) (name : K)
    (present : K → Action S E Bool) (demand : K → Action S E V)
    (check : V → Action S E Bool) (symbol : valid name = true) :
    slot
      (fun key => bind (admitName valid cause key) (fun _ => present key))
      (fun key => bind (admitName valid cause key) (fun _ => demand key))
      name check =
    slot present demand name check := by
  simp only [slot]
  have identity {A : Type} (action : Action S E A) :
      bind (admitName valid cause name) (fun _ => action) = action := by
    funext state
    simp [bind, admitName, symbol]
  rw [identity, identity]

-- A successful presence event can mutate the receiver, the value cell, or the
-- nested contract. A cached pre-event value would violate the ordinary order.
theorem demand_observes_post_presence_state (present : K → Action S E Bool)
    (demand : K → Action S E V) (name : K) (check : V → Action S E Bool)
    (before after : S) (found : present name before = (.ok true, after)) :
    slot present demand name check before = bind (demand name) check after := by
  simp [slot, bind, found]

-- The indexed local hit establishes the same value and empty nested capture.
-- The common continuation still authenticates and delivers the read. The
-- ordinary capture path continues to perform the revision check on a miss.
theorem local_hit_uses_same_finish (query : Action S E (Bool × List R))
    (finish : (Bool × List R) → Action S E A) (state : S)
    (hit : query state = (.ok (true, []), state)) :
    bind query finish state = finish (true, []) state := by
  simp [bind, hit]

-- An observed warm read may enter the existing value vector through its
-- admitted adapter. The proof covers only the lookup. Both paths retain the
-- original record delivery, and the next operation sees the callback's state.
def vectorRead (admitted : S → Bool) (ordinary vector : Action S E V)
    (deliverValue : V → Action S E A) : Action S E A :=
  bind (fun state => if admitted state then vector state else ordinary state) deliverValue

theorem vector_read_keeps_delivery (admitted : S → Bool)
    (ordinary vector : Action S E V) (deliverValue : V → Action S E A)
    (same : ∀ state, admitted state = true → vector state = ordinary state) :
    vectorRead admitted ordinary vector deliverValue = bind ordinary deliverValue := by
  funext state
  by_cases live : admitted state = true
  · simp [vectorRead, bind, live, same state live]
  · simp [vectorRead, bind, live]

example : slot (fun (_ : Unit) (_ : Bool) => ((.ok true : Except Unit Bool), false))
    (fun _ state => (.ok state, state)) () pureAction true = (.ok false, false) := rfl

-- The storage route must already be admitted. A missing or cold cell has no
-- stored value; a stored Scheme false is still a present value.
def storedSlot (admitted : Bool) (stored : Option V) (check : V → Bool) : Bool :=
  admitted && (stored.map check).getD false

theorem refused_route_skips_check (stored : Option V) (check : V → Bool) :
    storedSlot false stored check = false := rfl

theorem stored_false_is_present :
    storedSlot true (some false) (! ·) = true := rfl

theorem uncomputed_cell_is_not_a_value (check : V → Bool) :
    storedSlot true (none : Option V) check = false := rfl

-- Even a warm admitted cell can issue an observable semantic read.
example :
    slot (fun (_ : Unit) => pureAction true)
      (fun _ (reads : Nat) => (.ok false, reads + 1))
      () (fun value => pureAction (!value)) 0 =
      ((.ok true : Except Unit Bool), 1) := rfl

-- Cold storage refusal does not determine the ordinary contract outcome.
example :
    storedSlot true (none : Option Bool) id = false ∧
    slot (fun (_ : Unit) => pureAction true)
      (fun _ (reads : Nat) => (.ok true, reads + 1))
      () pureAction 0 = ((.ok true : Except Unit Bool), 1) := by
  exact ⟨rfl, rfl⟩

-- The same child identity can occur under the Generic, EffectiveMethod and
-- Frame contracts. Reuse the validation program, not a verdict: each
-- occurrence runs on the state left by all earlier observations.
def descriptorChecks (check : D → Action S E Bool) : List D → Action S E Bool
  | [] => pureAction true
  | head :: tail => chain (check head) (descriptorChecks check tail)

-- The proper-list preflight runs before any child check. For a singleton,
-- Gerbil andmap captures the empty tail before calling the child predicate.
-- Its remaining work is only to normalize the result to a Boolean.
theorem singleton_descriptor_check (check : D → Action S E Bool) (head : D) :
    descriptorChecks check [head] = check head := by
  funext state
  unfold descriptorChecks chain bind
  cases check head state with
  | mk result after =>
    cases result with
    | error _ => rfl
    | ok result => cases result <;> rfl

-- A malformed spine fails before the first child read. Longer proper lists
-- use the original walker. The singleton branch keeps the exact continuation
-- of the sole child, including rejection, exception, and observer effects.
def checkDescriptorList (check : D → Action S E Bool) :
    Option (List D) → Action S E Bool
  | none => pureAction false
  | some elements => descriptorChecks check elements

def checkSmallDescriptorList (check : D → Action S E Bool) :
    Option (List D) → Action S E Bool
  | none => pureAction false
  | some [] => pureAction true
  | some [head] => check head
  | some (head :: next :: tail) => descriptorChecks check (head :: next :: tail)

theorem small_descriptor_check_preserves_trace (check : D → Action S E Bool)
    (elements : Option (List D)) :
    checkSmallDescriptorList check elements = checkDescriptorList check elements := by
  cases elements with
  | none => rfl
  | some elements =>
    cases elements with
    | nil => rfl
    | cons head tail =>
      cases tail with
      | nil => exact (singleton_descriptor_check check head).symm
      | cons _ _ => rfl

-- In this trace, the outer receiver's generation stays fixed. Delivery at
-- the first occurrence changes the child after reading its old state.
private structure DeepCheckState where
  generation : Nat
  childValid : Bool
  observations : List Nat
  deriving DecidableEq

private def observeChild (identity : Nat) : Action DeepCheckState Unit Bool :=
  fun state => (.ok state.childValid,
    { state with childValid := false, observations := state.observations ++ [identity] })

theorem outer_generation_does_not_certify_repeated_child :
    descriptorChecks observeChild [42, 42] ⟨7, true, []⟩ =
      (.ok false, ⟨7, false, [42, 42]⟩) ∧
    descriptorChecks observeChild [42] ⟨7, true, []⟩ =
      (.ok true, ⟨7, false, [42]⟩) := by
  exact ⟨rfl, rfl⟩

-- A delivery route is chosen from the immutable observer list of one dynamic
-- scope. Choosing the route stores no result from a callback or signature.
def routeDelivery (run : Observer → Action S E Unit) (observers : List Observer) :
    Action S E Unit :=
  match observers with
  | [] => pureAction ()
  | [observer] => run observer
  | _ => deliver run observers

theorem route_delivery_exact (run : Observer → Action S E Unit)
    (observers : List Observer) :
    routeDelivery run observers = deliver run observers := by
  cases observers with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil =>
      funext state
      simp only [routeDelivery, deliver, bind]
      cases run first state with
      | mk result after => cases result <;> rfl
    | cons _ _ => rfl

-- Every occurrence registers and authenticates its own live evidence before
-- callback delivery. Callbacks run without an observer scope and can change
-- the state seen by the next check, even when both reads have the same identity.
def deliverOccurrences (admit : R → Action (Bool × S) E Unit)
    (callback : R → Observer → Action (Bool × S) E Unit)
    (route : (Observer → Action (Bool × S) E Unit) → List Observer →
      Action (Bool × S) E Unit)
    (observers : List Observer) : List R → Action (Bool × S) E Unit
  | [] => pureAction ()
  | read :: tail =>
    bind (admit read) fun _ =>
      bind (withoutRecording (route (callback read) observers)) fun _ =>
        deliverOccurrences admit callback route observers tail

theorem routed_occurrences_preserve_evidence_and_effects
    (admit : R → Action (Bool × S) E Unit)
    (callback : R → Observer → Action (Bool × S) E Unit)
    (observers : List Observer) (reads : List R) :
    deliverOccurrences admit callback routeDelivery observers reads =
      deliverOccurrences admit callback deliver observers reads := by
  induction reads with
  | nil => rfl
  | cons read rest ih =>
    simp only [deliverOccurrences, route_delivery_exact, ih]

-- A callback may tamper with a presented record while its identity and the
-- receiver's revision stay fixed. The second occurrence must authenticate
-- again, before the callback receives that occurrence.
private structure EvidenceState where
  revision : Nat
  presented : Bool
  deliveries : List Nat

private def authenticateOccurrence (_ : Nat) : Action (Bool × EvidenceState) Unit Unit :=
  fun state => (if state.2.presented then .ok () else .error (), state)

private def changePresentation (read : Nat) (_ : Unit) :
    Action (Bool × EvidenceState) Unit Unit :=
  fun (enabled, state) =>
    (.ok (), (enabled, { state with presented := false, deliveries := state.deliveries ++ [read] }))

theorem repeated_read_identity_does_not_certify_issuance :
    deliverOccurrences authenticateOccurrence changePresentation routeDelivery
      [()] [42, 42] (true, ⟨7, true, []⟩) =
      (.error (), (true, ⟨7, false, [42]⟩)) := rfl

-- C4's zero/one-parent cases with a singleton head and no reusable suffix.
-- The parent resolver can fail or run hooks. Both branches use it once at
-- the original point, then publish the child's head on that exact live order.
def extendPreparedParent (resolve : O → Action S E (List O)) (head : O)
    (parent : Option O) : Action S E (List O) :=
  match parent with
  | none => pureAction [head]
  | some parent => bind (resolve parent) (fun order => pureAction (head :: order))

def c4ShortHead (resolve : O → Action S E (List O)) (head : O)
    (parent : Option O) : Action S E (List O) :=
  match parent with
  | none => pureAction [head]
  | some parent => bind (resolve parent) (fun order => pureAction ([head] ++ order))

theorem extend_prepared_parent_preserves_effects
    (resolve : O → Action S E (List O)) (head : O) (parent : Option O)
    (publish : List O → Action S E A) :
    bind (extendPreparedParent resolve head parent) publish =
      bind (c4ShortHead resolve head parent) publish := by
  cases parent <;> rfl

-- Reuse is limited to the live parent resolution. An older C4 result cannot
-- stand in for it after a topology edit or a hook failure.
theorem extend_parent_after_update (resolve : O → Action S E (List O))
    (head parent : O) (before after : S) (order : List O)
    (live : resolve parent before = (.ok order, after)) :
    extendPreparedParent resolve head (some parent) before = (.ok (head :: order), after) := by
  simp [extendPreparedParent, bind, live, pureAction]

-- A dispatch artifact can stand in for the pure selection computation only
-- after live admission of every input on which that computation depends.
-- The returned effective method still runs on the live state and may fail.
def guardedDispatch [DecidableEq Key] (readKey : Action S E Key)
    (preparedKey : Key) (prepared : Plan) (compile : Key → Plan)
    (execute : Plan → Action S E A) : Action S E A :=
  bind readKey fun live =>
    execute (if live = preparedKey then prepared else compile live)

theorem guarded_dispatch_preserves_live_admission [DecidableEq Key]
    (readKey : Action S E Key) (preparedKey : Key) (prepared : Plan)
    (compile : Key → Plan) (execute : Plan → Action S E A)
    (valid : prepared = compile preparedKey) :
    guardedDispatch readKey preparedKey prepared compile execute =
      bind readKey (fun live => execute (compile live)) := by
  subst prepared
  unfold guardedDispatch
  congr 1
  funext live
  by_cases current : live = preparedKey
  · simp [current]
  · simp [current]

-- Changing an EQL target can change dispatch while the generic generation
-- remains the same. The full key rejects the old plan in that state.
example :
    guardedDispatch (pureAction (7, false)) (7, true) true Prod.snd
      (pureAction (S := Unit) (E := Unit)) () = (.ok false, ()) := rfl

-- A contract entered under read observation uses ordinary Slot operations
-- throughout that invocation. Scoped callbacks can run their own contracts,
-- but return to the caller's observation scope. No Slot verdict is retained.
def observedFields (test : F → Action S E Bool) : List F → Action S E Bool
  | [] => pureAction true
  | field :: tail => chain (test field) (observedFields test tail)

def liveFieldRoutes (active : S → Bool) (ordinary prepared : F → Action S E Bool)
    : List F → Action S E Bool
  | [] => pureAction true
  | field :: tail =>
      chain (fun s => if active s then ordinary field s else prepared field s)
        (liveFieldRoutes active ordinary prepared tail)

theorem observed_route_once (active : S → Bool) (ordinary prepared : F → Action S E Bool)
    (restores : ∀ field before after, active before = true →
      ordinary field before = (.ok true, after) → active after = true)
    (fields : List F) (before : S) (observed : active before = true) :
    liveFieldRoutes active ordinary prepared fields before =
      observedFields ordinary fields before := by
  induction fields generalizing before with
  | nil => rfl
  | cons field tail ih =>
    simp only [liveFieldRoutes, observedFields, chain, bind, observed, ite_true]
    cases step : ordinary field before with
    | mk result after =>
      cases result with
      | error cause => rfl
      | ok result =>
        cases result with
        | false => rfl
        | true => exact ih after (restores field before after observed step)

-- The route proof permits arbitrary writes, rejection and different records at
-- each occurrence. In particular a callback may change a later field even
-- though the original Type/observer route is still in force.
private def readLiveField (write : Bool) : Action (Bool × Bool × List Bool) Unit Bool :=
  fun (enabled, live, trace) => (.ok live, (enabled, write, trace ++ [live]))

example :
    observedFields readLiveField [false, true] (true, true, []) =
      (.ok false, (true, true, [true, false])) := rfl

-- An admission receipt may certify an immutable scalar after the original
-- demand. It cannot certify a mutable container by pointer identity.
def checkAdmittedValue [DecidableEq V] (test : V → Bool)
    (admitted live : V) : Bool :=
  if live = admitted then true else test live

theorem admitted_value_after_demand [DecidableEq V] (test : V → Bool)
    (admitted : V) (accepted : test admitted = true)
    (read : Action S E V) :
    bind read (fun live => pureAction (checkAdmittedValue test admitted live)) =
      bind read (fun live => pureAction (test live)) := by
  congr 1
  funext live
  by_cases same : live = admitted
  · simp [checkAdmittedValue, same, accepted]
  · simp [checkAdmittedValue, same]

-- A mutable list is a reference, so the receipt's value equality must be
-- semantic equality for the predicate, not equality of the reference.
private structure MethodListState where
  revision : Nat
  listIdentity : Nat
  validElement : Bool

private def replaceMethodListElement (state : MethodListState) : MethodListState :=
  { state with validElement := false }

theorem list_edit_preserves_owner_key_but_invalidates_contract :
    let state : MethodListState := ⟨7, 42, true⟩
    let after := replaceMethodListElement state
    (after.revision, after.listIdentity) = (state.revision, state.listIdentity) ∧
      state.validElement = true ∧ after.validElement = false := by
  exact ⟨rfl, rfl, rfl⟩

-- The owner and its Type invalidate a private admission through the POO
-- dependency index. A detached snapshot still needs a live value witness:
-- a write to an exposed list spine does not traverse that index.
structure DescriptorAdmission (V : Type) where
  revision : Nat
  value : V

def checkDescriptorAdmission [DecidableEq V] (test : V → Bool)
    (admission : DescriptorAdmission V) (revision : Nat) (live : V) : Bool :=
  if revision = admission.revision then checkAdmittedValue test admission.value live
  else test live

theorem descriptor_admission_after_callback [DecidableEq V] (test : V → Bool)
    (admission : DescriptorAdmission V) (accepted : test admission.value = true)
    (demand : Action S E V) (revision : S → Nat) :
    bind demand (fun live state =>
      pureAction (checkDescriptorAdmission test admission (revision state) live) state) =
    bind demand (fun live => pureAction (test live)) := by
  congr 1
  funext live state
  by_cases current : revision state = admission.revision
  · by_cases same : live = admission.value <;>
      simp [checkDescriptorAdmission, current, checkAdmittedValue, same, accepted]
  · simp [checkDescriptorAdmission, current]

theorem invalidated_descriptor_uses_live_check [DecidableEq V] (test : V → Bool)
    (admission : DescriptorAdmission V) (revision : Nat) (live : V)
    (changed : revision ≠ admission.revision) :
    checkDescriptorAdmission test admission revision live = test live := by
  simp [checkDescriptorAdmission, changed]

-- POO increments the dependent owner's revision for either source edge:
-- the descriptor or its Type. A rejected method edit leaves the installed
-- snapshot and revision intact. Successful publication starts a new receipt.
def publishDescriptor [DecidableEq V] (admit : V → Bool)
    (current : DescriptorAdmission V) (proposed : V) : DescriptorAdmission V :=
  if admit proposed then ⟨current.revision + 1, proposed⟩ else current

theorem refused_descriptor_update [DecidableEq V] (admit : V → Bool)
    (current : DescriptorAdmission V) (proposed : V) (refused : admit proposed = false) :
    publishDescriptor admit current proposed = current := by
  simp [publishDescriptor, refused]

theorem published_descriptor_discards_old_receipt [DecidableEq V] (admit : V → Bool)
    (current : DescriptorAdmission V) (proposed live : V) (accepted : admit proposed = true) :
    checkDescriptorAdmission admit current (publishDescriptor admit current proposed).revision live =
      admit live := by
  apply invalidated_descriptor_uses_live_check
  simp [publishDescriptor, accepted]

-- A known arity is sufficient to establish properness if the live list
-- ends at that exact bound. Otherwise use the ordinary proper-list check.
def endsAt (n : Nat) : List V → Bool
  | [] => n == 0
  | _ :: rest =>
    match n with
    | 0 => false
    | n + 1 => endsAt n rest

theorem endsAt_is_exact_arity (n : Nat) (values : List V) :
    endsAt n values = (values.length == n) := by
  induction values generalizing n with
  | nil => cases n <;> rfl
  | cons _ rest ih =>
    cases n with
    | zero => rfl
    | succ n => simp [endsAt, ih, List.length_cons]

-- Exact length validates the spine only. Every child predicate still runs
-- after the corresponding read and can reject an element changed in place.
theorem admitted_arity_keeps_child_actions (check : D → Action S E Bool)
    (arity : Nat) (live : List D) (ends : endsAt arity live = true) :
    (if endsAt arity live then descriptorChecks check live
     else checkDescriptorList check (some live)) =
      checkDescriptorList check (some live) := by
  simp [ends, checkDescriptorList]

example : checkDescriptorAdmission (fun keys : List Bool => keys.all id)
    ⟨7, [true]⟩ 7 [false] = false := rfl

-- Private keys and specializer rows are detached from the exposed list:
-- observers can change the latter without advancing the owner revision.
-- The original demand still runs and a rejected witness uses the live check.
def snapshotKeysCheck [DecidableEq K] (valid : K → Bool)
    (saved live : List K) : Bool :=
  if live = saved then true else live.all valid

theorem snapshot_keys_preserve_callback_result [DecidableEq K] (valid : K → Bool)
    (saved : List K) (accepted : saved.all valid = true)
    (read : Action S E (List K)) :
    bind read (fun live => pureAction (snapshotKeysCheck valid saved live)) =
      bind read (fun live => pureAction (live.all valid)) := by
  simpa [snapshotKeysCheck, checkAdmittedValue] using
    (admitted_value_after_demand (fun keys : List K => keys.all valid) saved accepted read)

-- The immutable row can establish a proper spine, but the Specializer
-- children must still run. A preceding child can change the next element.
-- The cursor, including its read/observer effects, belongs to the live list.
def checkSnapshotChildren (proper : Bool) (savedWidth liveWidth : Nat)
    (liveChecks : Action S E Bool) : Action S E Bool :=
  if liveWidth = savedWidth then liveChecks
  else if proper then liveChecks else pureAction false

theorem snapshot_children_keep_live_cursor (proper : Bool)
    (savedWidth liveWidth : Nat) (liveChecks : Action S E Bool)
    (exact : liveWidth = savedWidth → proper = true) :
    checkSnapshotChildren proper savedWidth liveWidth liveChecks =
      (if proper then liveChecks else pureAction false) := by
  by_cases hit : liveWidth = savedWidth
  · simp [checkSnapshotChildren, hit, exact hit]
  · simp [checkSnapshotChildren, hit]

-- A revision is sampled after the demand and observer. Any source edit
-- invalidates the snapshot before the next predicate uses it.
theorem native_edit_after_demand_uses_live_predicate [DecidableEq V]
    (test : V → Bool) (saved : DescriptorAdmission V) (demand : Action S E V)
    (revision : S → Nat) (before after : S) (value : V)
    (read : demand before = (.ok value, after))
    (invalidated : revision after ≠ saved.revision) :
    bind demand (fun live state =>
      pureAction (checkDescriptorAdmission test saved (revision state) live) state)
      before = (.ok (test value), after) := by
  simp [bind, read, pureAction, checkDescriptorAdmission, invalidated]

-- A descriptor Slot owns its sequence. Public .ref and the read inspector
-- each project a fresh ordinary list. Neither view is the signed payload.
private structure SequenceSlot (V : Type) where
  stored : List V
  revision : Nat
  view : List V

private def readSequenceView (slot : SequenceSlot V) : SequenceSlot V :=
  { slot with view := slot.stored }

private def editSequenceView (slot : SequenceSlot V) (view : List V) : SequenceSlot V :=
  { slot with view }

theorem editing_projected_list_keeps_slot_evidence
    (slot : SequenceSlot V) (edited : List V) :
    let after := editSequenceView (readSequenceView slot) edited
    (after.stored, after.revision) = (slot.stored, slot.revision) ∧
      (readSequenceView after).view = slot.stored := ⟨rfl, rfl⟩

-- Internal and public demand share exactly one issued read and delivery.
-- Converting the successful result does not interpret or construct evidence.
theorem projected_read_keeps_trace (read : Action S E V) (project : V → Public) :
    bind read (fun value => pureAction (project value)) =
      fun state =>
        let (outcome, after) := read state
        (outcome.map project, after) := by
  funext state
  unfold bind
  cases read state with
  | mk result after => cases result <;> rfl

-- A native edit replaces the current receiver's Slot and advances its
-- revision. A later demand uses that receiver's new sequence, even when
-- the observer ran during an earlier occurrence of the same Slot.
private def replaceSequence (slot : SequenceSlot V) (value : List V) : SequenceSlot V :=
  { slot with stored := value, revision := slot.revision + 1 }

theorem replace_sequence_invalidates_and_projects (slot : SequenceSlot V) (value : List V) :
    let after := replaceSequence slot value
    after.revision ≠ slot.revision ∧ (readSequenceView after).view = value := by
  exact ⟨Nat.succ_ne_self _, rfl⟩

-- A later demand must read the Slot again after a delivered observation
-- that publishes an edit. The first receipt still names its issued value.
theorem sequence_edit_during_delivery_keeps_receipt_and_rechecks
    (slot : SequenceSlot V) (replacement : List V) :
    let demand : Action (SequenceSlot V) E (Nat × List V) :=
      fun state => (.ok (state.revision, state.stored), state)
    bind demand (fun issued =>
      bind (fun state => (.ok (), replaceSequence state replacement)) (fun _ =>
        bind demand (fun live => pureAction (issued, live)))) slot =
      (.ok ((slot.revision, slot.stored), (slot.revision + 1, replacement)),
        replaceSequence slot replacement) := rfl

-- The vector retains owners and order only. Child predicates operate on the
-- current state, and their rejection/exception/observer effects are kept.
theorem owned_sequence_keeps_child_effects (check : V → Action S E Bool) (values : List V) :
    descriptorChecks check values.toArray.toList = descriptorChecks check values := by
  simp

private inductive MethodQualifier (Name : Type) where
  | primary
  | single (name : Name)
  | explicit (names : List Name)

private def qualifierNames : MethodQualifier Name → List Name
  | .primary => []
  | .single name => [name]
  | .explicit names => names

-- Specializer keys already implement class identity and EQL agreement.
-- Their ordered list also records the number of required parameters.
private structure MethodSignature (Name Key : Type) where
  qualifiers : MethodQualifier Name
  specializers : List Key

private def methodAgrees (left right : MethodSignature Name Key) : Prop :=
  qualifierNames left.qualifiers = qualifierNames right.qualifiers ∧
    left.specializers = right.specializers

theorem explicit_qualifier_replacement_iff (left right : List Name)
    (leftKeys rightKeys : List Key) :
    methodAgrees ⟨.explicit left, leftKeys⟩ ⟨.explicit right, rightKeys⟩ ↔
      left = right ∧ leftKeys = rightKeys := Iff.rfl

theorem copied_qualifier_replaces (names : List Name) (keys : List Key) :
    methodAgrees ⟨.explicit names, keys⟩ ⟨.explicit names.toArray.toList, keys⟩ := by
  simp [methodAgrees, qualifierNames]

theorem singleton_qualifier_agrees_with_shorthand (name : Name) (keys : List Key) :
    methodAgrees ⟨.single name, keys⟩ ⟨.explicit [name], keys⟩ := ⟨rfl, rfl⟩

theorem explicit_primary_is_qualified (name : Name) (keys : List Key) :
    ¬ methodAgrees ⟨.primary, keys⟩ ⟨.explicit [name], keys⟩ := by
  simp [methodAgrees, qualifierNames]

-- Publishing prepends the new method and removes exactly the agreeing rows.
theorem replacement_retains_exactly_nonagreeing_methods
    (signature : Method → MethodSignature Name Key) (new old : Method)
    (installed : List Method) (decideAgreement : Method → Bool)
    (correct : ∀ m, decideAgreement m = true ↔ methodAgrees (signature new) (signature m)) :
    old ∈ new :: installed.filter (fun m => !decideAgreement m) ↔
      old = new ∨ (old ∈ installed ∧ ¬ methodAgrees (signature new) (signature old)) := by
  simp [List.mem_filter, ← correct]

private def measureAll (measure : D × A → Action S E (Option R)) :
    List (D × A) → Action S E (List (Option R))
  | [] => pureAction []
  | pair :: rest => bind (measure pair) fun result =>
      bind (measureAll measure rest) fun results => pureAction (result :: results)

-- An inapplicable position does not end the effectful traversal. Vector
-- storage owns the spine; specializer actions still read their live targets.
theorem stored_zip_preserves_applicability_effects
    (measure : D × A → Action S E (Option R)) (descriptors : List D) (arguments : List A) :
    measureAll measure (descriptors.toArray.toList.zip arguments) =
      measureAll measure (descriptors.zip arguments) := by simp

theorem measure_visits_rest_after_inapplicable
    (measure : D × A → Action S E (Option R)) (pair : D × A) (rest : List (D × A))
    (before after : S) (miss : measure pair before = (.ok none, after)) :
    measureAll measure (pair :: rest) before =
      bind (measureAll measure rest) (fun values => pureAction (none :: values)) after := by
  simp [measureAll, bind, miss]

-- A union of already demanded key sequences is pure. Neither arrangement
-- changes membership or substitutes a key Slot read across a callback.
theorem stored_key_union_preserves_membership [DecidableEq K]
    (key : K) (sequence : List K) (other : List K) :
    key ∈ sequence.toArray.toList ++ other ↔ key ∈ sequence ∨ key ∈ other := by simp

private def readKeys (read : Owner → Action S E (List K)) :
    List Owner → Action S E (List (List K))
  | [] => pureAction []
  | owner :: rest => bind (read owner) fun keys =>
      bind (readKeys read rest) fun later => pureAction (keys :: later)

private def keywordResult [DecidableEq K] (contains exempt : K → Bool)
    (allow : Bool) (supplied : List K) : Option K :=
  if allow then none else supplied.find? (fun key => !(exempt key || contains key))

private def admitKeywords [DecidableEq K] (read : Owner → Action S E (List K))
    (allow : Action S E Bool) (wellFormed : Bool) (malformed : E)
    (members : List (List K) → K → Bool) (owners : List Owner)
    (exempt : K → Bool) (supplied : List K) : Action S E (Option K) :=
  if wellFormed then
    bind (readKeys read owners) fun keys =>
      bind allow fun allowed => pureAction (keywordResult (members keys) exempt allowed supplied)
  else fun state => (.error malformed, state)

private theorem keywordMembership [DecidableEq K] (key : K) (groups : List (List K)) :
    decide (key ∈ groups.flatten) = groups.any (fun keys => decide (key ∈ keys)) := by
  induction groups with
  | nil => rfl
  | cons keys rest ih =>
    simp only [List.flatten_cons, List.mem_append, List.any_cons, ← ih]
    by_cases first : key ∈ keys <;> simp [first]

-- The two programs demand the same owners in order. A read still observes
-- changes made by earlier reads, and final checks run after allow's effects.
-- Iteration on already demanded immutable data may change representation.
theorem keyword_vector_preserves_reads_and_first_rejection [DecidableEq K]
    (read : Owner → Action S E (List K)) (allow : Action S E Bool)
    (wellFormed : Bool) (malformed : E) (owners : List Owner)
    (exempt : K → Bool) (supplied : List K) :
    admitKeywords read allow wellFormed malformed
      (fun groups key => groups.any (fun keys => decide (key ∈ keys.toArray.toList)))
      owners exempt supplied =
    admitKeywords read allow wellFormed malformed
      (fun groups key => decide (key ∈ groups.flatten)) owners exempt supplied := by
  have same : (fun (groups : List (List K)) (key : K) =>
      groups.any (fun keys => decide (key ∈ keys.toArray.toList))) =
      (fun groups key => decide (key ∈ groups.flatten)) := by
    funext groups key
    simpa using (keywordMembership key groups).symm
  rw [same]

theorem malformed_keywords_refuse_before_key_demand [DecidableEq K]
    (read : Owner → Action S E (List K)) (allow : Action S E Bool)
    (malformed : E) (members : List (List K) → K → Bool) (owners : List Owner)
    (exempt : K → Bool) (supplied : List K) (before : S) :
    admitKeywords read allow false malformed members owners exempt supplied before =
      (.error malformed, before) := rfl

theorem keyword_second_demand_sees_callback_state
    (read : Owner → Action S E (List K)) (first second : Owner)
    (before after : S) (stored : List K) (firstDone : read first before = (.ok stored, after)) :
    readKeys read [first, second] before =
      bind (read second) (fun latest => pureAction [stored, latest]) after := by
  simp [readKeys, bind, firstDone, pureAction]
  cases read second after with
  | mk result state => cases result <;> rfl

end LeanPoo.Object.SlotContracts
