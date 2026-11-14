-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Prototype.SlotSpec
import LeanPoo.Object.Schema

namespace LeanPoo.Object.SlotPreparation

namespace EffectfulAdmission

/-- Native method installation can itself dispatch a mutable HashTable method.
Model that effect explicitly rather than treating protocol absence as purity. -/
def sweep {State Protocol Entry Result Error : Type}
    (protocol : State → Option Protocol)
    (hook : Protocol → Entry → State → Except Error (Entry × State))
    (write : Entry → State → Except Error (Result × State)) :
    List Entry → State → Except Error (List Result × State)
  | [], state => .ok ([], state)
  | entry :: rest, state => do
    let (selected, beforeWrite) ← match protocol state with
      | none => .ok (entry, state)
      | some selected => hook selected entry state
    let (result, afterWrite) ← write selected beforeWrite
    let (results, finalState) ← sweep protocol hook write rest afterWrite
    pure (result :: results, finalState)

def withoutHooks {State Entry Result Error : Type}
    (write : Entry → State → Except Error (Result × State)) :
    List Entry → State → Except Error (List Result × State)
  | [], state => .ok ([], state)
  | entry :: rest, state => do
    let (result, afterWrite) ← write entry state
    let (results, finalState) ← withoutHooks write rest afterWrite
    pure (result :: results, finalState)

/-- Derive this frame from the actual native write route. It is not a caller
purity flag. Error results and successful final state remain exactly equal. -/
theorem without_hooks_exact {State Protocol Entry Result Error : Type}
    (protocol : State → Option Protocol)
    (hook : Protocol → Entry → State → Except Error (Entry × State))
    (write : Entry → State → Except Error (Result × State))
    (preserves : ∀ entry state result after,
      protocol state = none → write entry state = .ok (result, after) →
      protocol after = none)
    (entries : List Entry) (state : State) (closed : protocol state = none) :
    sweep protocol hook write entries state = withoutHooks write entries state := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [sweep, closed, withoutHooks, Except.bind, Bind.bind]
    cases result : write entry state with
    | error cause => rfl
    | ok accepted =>
      rcases accepted with ⟨value, after⟩
      dsimp only
      rw [ih after (preserves entry state value after closed result)]

private def changingProtocol (state : Nat) : Option Unit :=
  if state = 0 then none else some ()

private def insertingWrite (entry state : Nat) : Except Unit (Nat × Nat) :=
  .ok (entry, state + 1)

private def observingHook (_ : Unit) (entry state : Nat) : Except Unit (Nat × Nat) :=
  .ok (entry + 100, state)

/-- A write installs a protocol between two slots. Initial absence alone
cannot justify hoisting selection out of the native installation loop. -/
theorem initial_absence_is_insufficient :
    changingProtocol 0 = none ∧
    sweep changingProtocol observingHook insertingWrite [0, 0] 0 ≠
      withoutHooks insertingWrite [0, 0] 0 := by
  change (none : Option Unit) = none ∧
    (Except.ok ([0, 100], 2) : Except Unit (List Nat × Nat)) ≠ .ok ([0, 0], 2)
  constructor
  · rfl
  · intro same
    cases same

end EffectfulAdmission

namespace PayloadCapture

/-- Handles identify actual required validation/capture fields, not only their
owner revision. The producer supplies the original scheduled reads for one
closed phase; author callbacks are separate boundaries. This is not every
reachable field: a shadowed payload the producer never reads is not added. -/
abbrev SourceRef (Key Handle : Type) := Key × Handle

/-- One source cut supplies field payloads (or their original admission error).
Capture every scheduled row in order, including a shadowed contribution's tag
when stock admission validates it. Payloads the stock compiler discards need
not be captured. Values may themselves be references/functions: only the
payload is copied, not its reachable store or a computed receiver value. -/
def capture {Key Handle Error : Type} {Payload : Key → Type}
    [DecidableEq Key]
    (read : (key : Key) → Handle → Except Error (Payload key)) :
    List (SourceRef Key Handle) → Except Error (List (Entry Key Payload))
  | [] => .ok []
  | (key, handle) :: rest => do
    let payload ← read key handle
    let tail ← capture read rest
    Except.ok (⟨key, payload, fun query => inferInstanceAs (Decidable (query = key))⟩ :: tail)

/-- Logical read work for that same closed capture. A failed field ends the
walk; its suffix is not charged or evaluated by capture. This is not a runtime
timer or a claim that a payload read is constant-time. -/
def reads {Key Handle Error : Type} {Payload : Key → Type}
    (read : (key : Key) → Handle → Except Error (Payload key)) :
    List (SourceRef Key Handle) → Nat
  | [] => 0
  | (key, handle) :: rest =>
    match read key handle with
    | .error _ => 1
    | .ok _ => 1 + reads read rest

/-- Successful admission cannot skip any source field merely because its
key is not demanded. This bound applies to the producer's required read
schedule, not every possible source field. Sharing saves repetitions, not
this first walk. -/
theorem successful_capture_reads_all {Key Handle Error : Type}
    {Payload : Key → Type}
    [DecidableEq Key]
    (read : (key : Key) → Handle → Except Error (Payload key))
    (refs : List (SourceRef Key Handle)) (captured : List (Entry Key Payload))
    (accepted : capture read refs = .ok captured) :
    reads read refs = refs.length := by
  induction refs generalizing captured with
  | nil => rfl
  | cons ref rest ih =>
    rcases ref with ⟨key, handle⟩
    cases found : read key handle with
    | error cause => simp [capture, found, Except.bind, Bind.bind] at accepted
    | ok payload =>
      cases tail : capture read rest with
      | error cause => simp [capture, found, tail, Except.bind, Bind.bind] at accepted
      | ok values =>
        simp only [reads, found]
        rw [ih values tail]
        simp [Nat.add_comm]

/-- The captured read schedule preserves order and membership (including
repeated keys). This is not the final deduplicated slot shape. A demand must
not filter required invalid siblings out of this scheduled admission. -/
theorem capture_preserves_keys {Key Handle Error : Type} {Payload : Key → Type}
    [DecidableEq Key]
    (read : (key : Key) → Handle → Except Error (Payload key))
    (refs : List (SourceRef Key Handle)) (captured : List (Entry Key Payload))
    (accepted : capture read refs = .ok captured) :
    captured.map Entry.key = refs.map Prod.fst := by
  induction refs generalizing captured with
  | nil => cases accepted; rfl
  | cons ref rest ih =>
    rcases ref with ⟨key, handle⟩
    cases found : read key handle with
    | error cause => simp [capture, found, Except.bind, Bind.bind] at accepted
    | ok payload =>
      cases tail : capture read rest with
      | error cause => simp [capture, found, tail, Except.bind, Bind.bind] at accepted
      | ok values =>
        simp only [capture, found, tail, Except.bind, Bind.bind] at accepted
        cases accepted
        simp only [List.map_cons]
        rw [ih values tail]

/-- Transport uses equality of the actual reads at every referenced handle.
Writes outside this support are immaterial. A containing receiver revision,
sealed flag or successful earlier query is not this premise. -/
theorem capture_frame {Key Handle Error : Type} {Payload : Key → Type}
    [DecidableEq Key]
    (before after : (key : Key) → Handle → Except Error (Payload key))
    (refs : List (SourceRef Key Handle))
    (same : ∀ ref ∈ refs, before ref.1 ref.2 = after ref.1 ref.2) :
    capture before refs = capture after refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih =>
    rcases ref with ⟨key, handle⟩
    have head := same (key, handle) (by simp)
    have tail := ih (fun ref member => same ref (by simp [member]))
    simp only [capture, head, tail]

/-- Keeping the captured prefix permits composition without changing which
error is first. This is ordered capture, not per-key validation. -/
theorem capture_append {Key Handle Error : Type} {Payload : Key → Type}
    [DecidableEq Key]
    (read : (key : Key) → Handle → Except Error (Payload key))
    (front back : List (SourceRef Key Handle)) :
    capture read (front ++ back) = (do
      let first ← capture read front
      let second ← capture read back
      Except.ok (first ++ second)) := by
  induction front with
  | nil =>
    simp only [List.nil_append, capture, Except.bind, Bind.bind]
    cases capture read back <;> rfl
  | cons ref rest ih =>
    rcases ref with ⟨key, handle⟩
    cases head : read key handle with
    | error cause => simp [capture, head, Except.bind, Bind.bind]
    | ok value =>
      simp only [List.cons_append, capture, head, Except.bind, Bind.bind]
      rw [ih]
      cases first : capture read rest <;>
      cases second : capture read back <;> rfl

private def checkedField (_key handle : Nat) : Except Nat Nat :=
  if handle = 0 then .ok 7 else .error handle

/-- A valid requested key is not an admission certificate: an unrelated
invalid contribution must still refuse whole preparation. -/
theorem unrelated_invalid_field_cannot_be_skipped :
    capture checkedField [(0, 0), (1, 1)] = .error 1 ∧
    (capture checkedField [(0, 0)]).isOk = true := by
  constructor <;> rfl

/-- Two invalid siblings retain their original source order. An index for a
demanded key cannot silently reorder whole-preparation diagnostics. -/
theorem first_invalid_field_retains_order :
    capture checkedField [(0, 2), (1, 1)] = .error 2 ∧
    capture checkedField [(1, 1), (0, 2)] = .error 1 := by
  constructor <;> rfl

private def beforeCallback (_key _handle : Nat) : Except Nat Nat := .ok 7
private def afterCallback (_key _handle : Nat) : Except Nat Nat := .ok 9

/-- An author callback replaces a constant SlotSpec's payload. Capturing on
later key demand is observably different from the stock pre-hook capture. -/
theorem capture_cannot_move_across_callback :
    (capture beforeCallback [(0, 0)]).map (fun xs => xs.map Entry.value) ≠
    (capture afterCallback [(0, 0)]).map (fun xs => xs.map Entry.value) := by
  change (Except.ok [7] : Except Nat (List Nat)) ≠ .ok [9]
  intro same
  have lists := Except.ok.inj same
  have heads := List.cons.inj lists
  exact (by decide : (7 : Nat) ≠ 9) heads.1

end PayloadCapture

namespace CapturedBinding

/-- Method cells distinguish a procedure from a malformed thunk payload.
Computed bodies may inspect or invoke their exact inherited cell. A bad
self/computed function is represented by a body that fails when invoked,
not an invented preparation-time rejection. -/
inductive Target (Value : Type) where
  | procedure (body : Unit → Value)
  | nonCallable

def Target.callable {Value : Type} : Target Value → Bool
  | .procedure _ => true
  | .nonCallable => false

/-- The four stock SlotSpec constructors AFTER their original tag admission
and payload capture. No author getter, declaration callback or hook runs here.
Opaque Value may include references or an effectful computation; binding
does not invoke any slot body. -/
inductive Spec (Self Value : Type) where
  | constant (value : Value)
  | thunk (target : Target Value)
  | self (body : Self → Value)
  | computed (body : Self → Target Value → Value)

/-- The ordinary apply-slot-spec step, retaining native lazy parent behavior.
The inherited cell is not invoked while constructing a child procedure. -/
def bind {Self Value : Type} (receiver : Self) :
    Spec Self Value → Target Value → Target Value
  | .constant value, _ => .procedure (fun _ => value)
  | .thunk target, _ => target
  | .self body, _ => .procedure (fun _ => body receiver)
  | .computed body, inherited => .procedure (fun _ => body receiver inherited)

/-- Classify the final procedure without constructing its receiver closure.
This checks only what stock binding checks: a malformed inner thunk may be
hidden, whereas a malformed final thunk must refuse on the hook-free path. -/
def classified {Self Value : Type} : Spec Self Value → Bool
  | .thunk target => target.callable
  | _ => true

theorem bind_callable {Self Value : Type} (receiver : Self)
    (spec : Spec Self Value) (inherited : Target Value) :
    (bind receiver spec inherited).callable = classified spec := by
  cases spec <;> rfl

def bindChain {Self Value : Type} (receiver : Self)
    (specs : List (Spec Self Value)) (inherited : Target Value) : Target Value :=
  specs.foldl (fun previous spec => bind receiver spec previous) inherited

def classifyChain {Self Value : Type}
    (specs : List (Spec Self Value)) (inherited : Bool) : Bool :=
  specs.foldl (fun _ spec => classified spec) inherited

/-- An exact rejection test for arbitrary captured chains, receivers and
inherited cells. It allocates no receiver method closure and evaluates no
business body. The law does not omit earlier source/tag admission. -/
theorem chain_callable_exact {Self Value : Type} (receiver : Self)
    (specs : List (Spec Self Value)) (inherited : Target Value) :
    (bindChain receiver specs inherited).callable =
      classifyChain specs inherited.callable := by
  induction specs generalizing inherited with
  | nil => rfl
  | cons spec rest ih =>
    change (bindChain receiver rest (bind receiver spec inherited)).callable =
      classifyChain rest (classified spec)
    rw [ih, bind_callable]

/-- Native contribution chains already store the most-specific entry first.
Checking that captured head is constant structural work per key; no scan of
the retained suffix and no receiver closure is needed. -/
def classifyNewest {Self Value : Type} : List (Spec Self Value) → Bool → Bool
  | [], inherited => inherited
  | spec :: _, _ => classified spec

theorem newest_callable_exact {Self Value : Type} (receiver : Self)
    (newestFirst : List (Spec Self Value)) (inherited : Target Value) :
    (bindChain receiver newestFirst.reverse inherited).callable =
      classifyNewest newestFirst inherited.callable := by
  cases newestFirst with
  | nil => rfl
  | cons spec rest =>
    simp only [bindChain, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil, bind_callable, classifyNewest]

def firstRefusal {Key : Type} : List (Key × Bool) → Except Key Unit
  | [] => .ok ()
  | (key, callable) :: rest => if callable then firstRefusal rest else .error key

/-- Eager binding for every key followed by the original ordered callable
checks has exactly the same acceptance/first error as classification of the
captured chains. Native enumeration and callback-free routes remain premises
of the adapter; no protocol-presence Boolean is trusted from a caller. -/
theorem all_keys_refusal_exact {Key Self Value : Type} (receiver : Self)
    (rows : List (Key × List (Spec Self Value))) (inherited : Target Value) :
    firstRefusal (rows.map fun row =>
      (row.1, (bindChain receiver row.2.reverse inherited).callable)) =
    firstRefusal (rows.map fun row =>
      (row.1, classifyNewest row.2 inherited.callable)) := by
  congr 1
  apply List.map_congr_left
  intro row _
  rw [newest_callable_exact]

/-- A final constant hides a malformed thunk; a computed wrapper is itself
callable even if its body will later report a failure. Neither case permits
inventing an eager validation of unused author functions. -/
theorem retained_wrapper_is_not_an_eager_body_check :
    classifyChain (Self := Unit) (Value := Nat)
      [.thunk .nonCallable, .constant 7] true = true ∧
    classifyChain (Self := Unit) (Value := Nat)
      [.thunk .nonCallable, .computed (fun _ _ => 9)] true = true := by
  constructor <;> rfl

/-- The classifier is invalid across an author hook: a hook can replace a
non-callable next result with a valid procedure before stock validation. -/
theorem hooks_can_repair_a_noncallable_result :
    Target.callable (Target.nonCallable : Target Nat) = false ∧
    Target.callable ((fun (_ : Target Nat) => .procedure (fun _ => 7))
      .nonCallable) = true := by
  constructor <;> rfl

end CapturedBinding

namespace PendingMethod

/-- One existing method cell, not a second store of business results. A
successful atomic publication retires the captured recipe in the same step. -/
inductive Cell (Recipe Method : Type) where
  | pending (recipe : Recipe)
  | ready (method : Method)

/-- Binding may allocate a fresh procedure identity. Only private allocation
state is available to it; native correspondence must derive this frame from
the captured SlotSpec kernel, not a caller purity declaration. -/
def force {Recipe Method Alloc Error : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (cell : Cell Recipe Method) (allocation : Alloc) :
    Except Error Method × Cell Recipe Method × Alloc :=
  match cell with
  | .ready method => (.ok method, cell, allocation)
  | .pending recipe =>
      let (result, next) := materialize recipe allocation
      match result with
      | .error cause => (.error cause, cell, next)
      | .ok method => (.ok method, .ready method, next)

theorem force_ready {Recipe Method Alloc Error : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (method : Method) (allocation : Alloc) :
    force materialize (.ready method) allocation =
      (.ok method, .ready method, allocation) := rfl

/-- The successful cell contains exactly the returned identity, even when
the allocator can create a different identity on every materialization. -/
theorem success_installs_identity {Recipe Method Alloc Error : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (cell : Cell Recipe Method) (allocation : Alloc) (method : Method)
    (accepted : (force materialize cell allocation).1 = .ok method) :
    (force materialize cell allocation).2.1 = .ready method := by
  cases cell with
  | ready previous => cases accepted; rfl
  | pending recipe =>
    cases result : materialize recipe allocation with
    | mk value next =>
      cases value with
      | error cause => simp [force, result] at accepted
      | ok found =>
        simp only [force, result, Except.ok.injEq] at accepted
        cases accepted
        simp [force, result]

/-- Every linearization of concurrent first forces returns the winner after
one success. Unrelated intervening allocations cannot change that identity. -/
theorem force_after_success {Recipe Method Alloc Error : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (cell : Cell Recipe Method) (allocation nextAllocation : Alloc) (method : Method)
    (accepted : (force materialize cell allocation).1 = .ok method) :
    force materialize (force materialize cell allocation).2.1 nextAllocation =
      (.ok method, .ready method, nextAllocation) := by
  rw [success_installs_identity materialize cell allocation method accepted]
  rfl

/-- User invocation follows the method publication boundary. Its arbitrary
result may itself encode body errors; its world effects are not rolled back.
The method cell never contains that result. -/
def call {Recipe Method Alloc Error World Result : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (invoke : Method → World → Result × World)
    (cell : Cell Recipe Method) (allocation : Alloc) (world : World) :
    (Except Error Result × World) × Cell Recipe Method × Alloc :=
  let (bound, nextCell, nextAllocation) := force materialize cell allocation
  match bound with
  | .error cause => ((.error cause, world), nextCell, nextAllocation)
  | .ok method =>
      let (result, nextWorld) := invoke method world
      ((.ok result, nextWorld), nextCell, nextAllocation)

theorem call_ready {Recipe Method Alloc Error World Result : Type}
    (materialize : Recipe → Alloc → Except Error Method × Alloc)
    (invoke : Method → World → Result × World)
    (method : Method) (allocation : Alloc) (world : World) :
    call materialize invoke (.ready method) allocation world =
      ((.ok (invoke method world).1, (invoke method world).2), .ready method, allocation) := rfl

private def freshMethod (_ : Unit) (allocation : Nat) : Except Unit Nat × Nat :=
  (.ok allocation, allocation + 1)

/-- Repeated body invocation has different results and effects while method
identity remains stable. Memoizing the business result in this cell is wrong. -/
theorem method_memoization_is_not_result_memoization :
    call freshMethod (fun _ count => (count, count + 1))
      (.pending ()) 0 0 = ((.ok 0, 1), .ready 0, 1) ∧
    call freshMethod (fun _ count => (count, count + 1))
      (.ready 0) 17 1 = ((.ok 1, 2), .ready 0, 17) := by
  constructor <;> rfl

/-- A body failure retains the published method and the body's world effect.
It must not turn the method cell into a cached failure or rerun binding. -/
theorem body_failure_retains_method :
    call freshMethod (fun _ count => ((Except.error 7 : Except Nat Nat), count + 1))
      (.pending ()) 0 0 = ((.ok (.error 7), 1), .ready 0, 1) := rfl

end PendingMethod

-- In the absence of a protocol, the old per-slot C4 walk visits the complete
-- receiver precedence list. The stock lane makes that same check once.
def stockProtocolVisits (precedence slots : Nat) : Nat :=
  if slots = 0 then 0 else precedence

theorem stock_protocol_visits_bound (precedence slots : Nat) :
    stockProtocolVisits precedence slots ≤ slots * precedence := by
  cases slots with
  | zero => simp [stockProtocolVisits]
  | succ n => simp [stockProtocolVisits, Nat.succ_mul]


end LeanPoo.Object.SlotPreparation

