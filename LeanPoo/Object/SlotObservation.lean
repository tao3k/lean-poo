import LeanPoo.Prototype.DictionaryBridge

/-! Canonical packing of the existing slot-observation scope. The host supplies
lexical parameterization and faithful frame/callback identities. No VM timing,
thread scheduler, collector or arbitrary continuation semantics are inferred. -/
namespace LeanPoo.Object
universe u v w

/-- The three existing dynamic values, including opaque frame and callback data. -/
structure ReadScope (Frame : Type u) (Observer : Type v) (Check : Type w) where
  frame : Option Frame
  observers : List Observer
  prechecks : List Check

variable {Frame : Type u} {Observer : Type v} {Check : Type w}

/-- Disabled observation clears every channel together. -/
def emptyReadScope : ReadScope Frame Observer Check := ⟨none, [], []⟩

/-- The ordinary disabled path uses no allocated context; active scopes retain
all original payloads. No comparison between callbacks is required. -/
def packReadScope : ReadScope Frame Observer Check → Option (Sum Frame (ReadScope Frame Observer Check))
  | ⟨none, [], []⟩ => none
  | ⟨some frame, [], []⟩ => some (.inl frame)
  | scope => some (.inr scope)

/-- Interpret the optional context using the original three-channel interface. -/
def unpackReadScope : Option (Sum Frame (ReadScope Frame Observer Check)) → ReadScope Frame Observer Check
  | none => emptyReadScope
  | some (.inl frame) => ⟨some frame, [], []⟩
  | some (.inr scope) => scope

/-- Packing preserves every callback, order, precheck and exact frame payload. -/
theorem unpackReadScope_pack (scope : ReadScope Frame Observer Check) :
    unpackReadScope (packReadScope scope) = scope := by
  cases scope with
  | mk frame observers prechecks =>
    cases frame <;> cases observers <;> cases prechecks <;> rfl

/-- Reuse the existing representation bridge over canonical optional contexts.
An allocated but completely empty context is not a second representation. -/
def readScopeBridge : Prototype.DictionaryBridge (ReadScope Frame Observer Check)
    {packed : Option (Sum Frame (ReadScope Frame Observer Check)) //
      packReadScope (unpackReadScope packed) = packed} where
  toFields scope := ⟨packReadScope scope, congrArg packReadScope (unpackReadScope_pack scope)⟩
  fromFields packed := unpackReadScope packed.val
  from_to := unpackReadScope_pack
  to_from packed := Subtype.ext packed.property

/-- Installing an observer shares the caller's capture frame and prepends its
optional precheck, keeping inner-before-outer callback order. -/
def observeReadScope (scope : ReadScope Frame Observer Check) (observer : Observer)
    (before : Option Check) : ReadScope Frame Observer Check :=
  { scope with observers := observer :: scope.observers
               prechecks := match before with | none => scope.prechecks | some check => check :: scope.prechecks }

/-- Recording replaces only the capture frame; observer and precheck payloads
remain the same original values rather than reconstructed approvals. -/
def captureReadScope (scope : ReadScope Frame Observer Check) (frame : Frame) : ReadScope Frame Observer Check :=
  { scope with frame := some frame }

/-- Both entry operations create an active optional context, including an empty
observer list when an actual capture frame is installed. -/
theorem observeReadScope_active (scope : ReadScope Frame Observer Check)
    (observer : Observer) (before : Option Check) :
    packReadScope (observeReadScope scope observer before) = some (.inr (observeReadScope scope observer before)) := by
  cases scope with
  | mk frame observers prechecks => cases frame <;> rfl

theorem captureReadScope_active (scope : ReadScope Frame Observer Check) (frame : Frame) :
    (packReadScope (captureReadScope scope frame)).isSome = true := by
  cases scope with
  | mk old observers prechecks => cases observers <;> cases prechecks <;> rfl

/-- Capture without observers reuses the original frame rather than allocating
an additional context record. Its frame/collection allocation is still charged. -/
theorem captureReadScope_frameOnly (frame : Frame) :
    packReadScope (captureReadScope (emptyReadScope : ReadScope Frame Observer Check) frame) =
      some (.inl frame) := rfl

/-- Any interpreted consumer keeps its entire result, including an Except cause
or an explicit ordered event trace. The caller's lexical scope is unchanged. -/
theorem readScope_consumer (caller scope : ReadScope Frame Observer Check)
    (consume : ReadScope Frame Observer Check → Result) :
    (consume (unpackReadScope (packReadScope scope)), caller) = (consume scope, caller) := by
  rw [unpackReadScope_pack]

/-- Already disabled consumers run directly at precisely the original empty
scope, preserving multiple returned values and errors in their interpretation. -/
theorem emptyReadScope_consumer (consume : ReadScope Frame Observer Check → Result) :
    consume (unpackReadScope none) = consume emptyReadScope := rfl

/-- Source-primitive accounting for disabled calls, read delivery and capture
entry. Frame allocation and callback/storage work are shared and excluded here.
One capture under existing observers can add lookup/tag/field/allocation work;
its complete premium remains on the bound, even when hot paths become cheaper.
The hypotheses price concrete primitives, not entire desired workflow totals. -/
theorem readScope_cost_bound (disabled deliveries captures lookup binding tag field allocation : Nat)
    (lookup_price : lookup ≤ 3 * binding) (delivery_price : tag + 2 * field ≤ lookup) :
    disabled * lookup + deliveries * (lookup + tag + 2 * field) +
        captures * (lookup + tag + 2 * field + allocation) ≤
      3 * (disabled * binding) + 2 * (deliveries * lookup) +
        captures * (lookup + tag + 2 * field + allocation) := by
  have disabled_bound : disabled * lookup ≤ 3 * (disabled * binding) := by
    simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left disabled lookup_price
  have delivery_bound : deliveries * (lookup + tag + 2 * field) ≤
      2 * (deliveries * lookup) := by
    simpa only [Nat.mul_add, Nat.two_mul, Nat.add_assoc] using
      Nat.mul_le_mul_left deliveries (Nat.add_le_add_left delivery_price lookup)
  exact Nat.add_le_add_right (Nat.add_le_add disabled_bound delivery_bound) _

/-- A successful nested capture records already-delivered reads into the parent
frame. The supplied record operation implements that frame's existing occurrence
or unique-root policy; it cannot invoke observers or change their identities. -/
def recordCapturedReads (scope : ReadScope Frame Observer Check) (roots : List Read)
    (record : Frame → List Read → Frame) : ReadScope Frame Observer Check :=
  { scope with frame := scope.frame.map (fun frame => record frame roots) }

/-- Parent observers keep their exact order and identities; none are replayed. -/
theorem recordCapturedReads_observers (scope : ReadScope Frame Observer Check) (roots : List Read)
    (record : Frame → List Read → Frame) :
    (recordCapturedReads scope roots record).observers = scope.observers := rfl

/-- Registration does not replace prechecks from the enclosing dynamic scope. -/
theorem recordCapturedReads_prechecks (scope : ReadScope Frame Observer Check) (roots : List Read)
    (record : Frame → List Read → Frame) :
    (recordCapturedReads scope roots record).prechecks = scope.prechecks := rfl

/-- Without an outer collector, recording cannot manufacture one. -/
theorem recordCapturedReads_no_frame (observers : List Observer) (checks : List Check)
    (roots : List Read) (record : Frame → List Read → Frame) :
    recordCapturedReads (⟨none, observers, checks⟩ : ReadScope Frame Observer Check) roots record =
      ⟨none, observers, checks⟩ := rfl

/-- Ordinary capture preserves original order and repeated occurrences. Unique
capture instead supplies its own existing identity-deduplication operation. -/
theorem recordCapturedReads_append (before roots : List Read) (observers : List Observer)
    (checks : List Check) :
    (recordCapturedReads (⟨some before, observers, checks⟩ : ReadScope (List Read) Observer Check)
      roots (· ++ ·)).frame = some (before ++ roots) := rfl

/-- Run prechecks in scope order, supplying the original query key to each.
A callback's edited copy can appear in its effects but does not become the
next callback's input. The supplied step models those external effects. -/
def checkDemand (key : Key) (checks : List (Key → State → Except Error State))
    (state : State) : Except Error (Key × State) :=
  (checks.foldlM (fun current (check : Key → State → Except Error State) => check key current) state).map (key, ·)

/-- A successful demand preserves the canonical key for lookup and issuance. -/
theorem checkDemand_key (key : Key) (checks : List (Key → State → Except Error State))
    (state final : State) (published : Key)
    (ready : checkDemand key checks state = .ok (published, final)) : published = key := by
  unfold checkDemand at ready
  cases h : checks.foldlM (m := Except Error)
    (fun current (check : Key → State → Except Error State) => check key current) state <;>
    simp_all [Except.map]

/-- The first precheck's refusal prevents later checks and keeps its cause. -/
theorem checkDemand_refusal (key : Key) (check : Key → State → Except Error State)
    (rest : List (Key → State → Except Error State)) (state : State)
    (refused : check key state = .error cause) :
    checkDemand key (check :: rest) state = .error cause := by
  simp [checkDemand, List.foldlM, refused, bind, Except.bind, Except.map]

/-- A structural read separates the index key, presented key and source
revision. Lists model finite spines by value. Host allocation must provide
separate mutable spines at issuance and public delivery. -/
structure IssuedReadKey (Name : Type u) where
  indexed : List Name
  presented : List Name
  revision : Nat

/-- Authenticate the presented key and check the current source revision. -/
def IssuedReadKey.current [DecidableEq Name] (read : IssuedReadKey Name)
    (revision : Nat) : Prop :=
  read.presented = read.indexed ∧ read.revision = revision

/-- A public consumer sees only a copy of the key. Its returned state does
not replace any of the signed record or index fields. -/
def IssuedReadKey.deliver (read : IssuedReadKey Name)
    (consume : List Name → State → State) (state : State) : IssuedReadKey Name × State :=
  (read, consume read.presented state)

/-- Editing a delivered key preserves both credentials and indexed identity. -/
theorem IssuedReadKey.deliver_current [DecidableEq Name] (read : IssuedReadKey Name)
    (consume : List Name → State → State) (state : State) (revision : Nat) :
    (read.deliver consume state).1.current revision ↔ read.current revision := Iff.rfl

/-- Direct tampering cannot change the independent index or authenticate the
new name. This models raw mutation of the stored presented spine. -/
theorem IssuedReadKey.tampered [DecidableEq Name] (read : IssuedReadKey Name)
    (edited : List Name) (different : edited ≠ read.indexed) (revision : Nat) :
    ({read with presented := edited}).indexed = read.indexed ∧
      ¬ ({read with presented := edited}).current revision :=
  ⟨rfl, fun accepted => different accepted.1⟩

/-- Even unmodified credentials become stale on a source revision change. -/
theorem IssuedReadKey.revision_stale [DecidableEq Name] (read : IssuedReadKey Name)
    (revision : Nat) (changed : read.revision ≠ revision) : ¬ read.current revision :=
  fun accepted => changed accepted.2

/-- Reobservation runs its work first, then admits the record at delivery.
The admission result is supplied by the existing issuance and revision checks. -/
def reobserveRead (work : State → State) (admit : State → Except Error Record)
    (deliver : Record → State → State) (state : State) : Except Error State :=
  let next := work state
  (admit next).map (fun read => deliver read next)

/-- A record damaged by work cannot reach its delivery callback. -/
theorem reobserveRead_refusal (work : State → State) (admit : State → Except Error Record)
    (deliver : Record → State → State) (state : State)
    (refused : admit (work state) = .error cause) :
    reobserveRead work admit deliver state = .error cause := by
  simp [reobserveRead, refused, Except.map]

/-- A consumer can edit its own names and parent lists. The same original lists
and parent identities remain available to a later replay. Lists model contents,
and the host provides detached mutable spines. -/
theorem issuedRead_payload_frame (names : List Name) (parents : List Parent)
    (consume : List Name → List Parent → State → State) (state : State) :
    ((names, parents), consume names parents state).1 = (names, parents) := rfl

namespace FixedReplay

inductive Failure where
  | unissued (record : Nat)
  | stale (record : Nat)
  deriving DecidableEq

structure Record where
  identity : Nat
  issued : Bool
  current : Bool

def validate (records : List Record) : Except Failure Nat := do
  match records.find? (fun read => !read.issued) with
  | some read => throw (.unissued read.identity)
  | none =>
    match records.find? (fun read => !read.current) with
    | some read => throw (.stale read.identity)
    | none => pure records.length

def protectedCount (before after : List Record) : Except Failure Nat := do
  let count ← validate before
  let _ ← validate after
  pure count

/-- The callback-free case may use one live validation. An arbitrary callback
may change any record and therefore supplies an independent return state. -/
theorem fixed_count_eq_protected (reads : List Record) :
    protectedCount reads reads = validate reads := by
  cases result : validate reads <;> simp [protectedCount, result] <;> rfl

theorem issuance_precedes_live_refusal (older forged : Nat) :
    validate [⟨older, true, false⟩, ⟨forged, false, true⟩] =
      .error (.unissued forged) := rfl

theorem open_count_needs_return_validation (record : Nat) :
    protectedCount [⟨record, true, true⟩] [⟨record, true, false⟩] =
      .error (.stale record) := rfl

end FixedReplay

end LeanPoo.Object

namespace LeanPoo.Object.PassiveDelivery

def invoke (effect : Observer → State → State) (observers : List Observer) (state : State) : State :=
  observers.foldl (fun state observe => effect observe state) state

def selected [DecidableEq Observer] (passive : Observer) (effect : Observer → State → State)
    (observers : List Observer) (state : State) : State :=
  if observers = [passive] then state else invoke effect observers state

theorem singleton_delivery_exact [DecidableEq Observer] (passive : Observer)
    (effect : Observer → State → State) (passiveEffect : ∀ state, effect passive state = state)
    (observers : List Observer) (state : State) :
    selected passive effect observers state = invoke effect observers state := by
  by_cases exactPassive : observers = [passive]
  · simp [selected, exactPassive, invoke, passiveEffect]
  · simp [selected, exactPassive]

end LeanPoo.Object.PassiveDelivery
namespace LeanPoo.Object.CheckpointEntry

/-- The signed read sequence and its fields are stable between native
issuance preflight and the first live check. Every admitted member has
already passed issuance, so removing only that immediate duplicate
check preserves the first refused read. The checkpoint can change
state, and its post-check therefore starts with independent evidence. -/
theorem first_refusal_after_issuance (reads : List Read)
    (issued live : Read → Bool)
    (preflight : ∀ read ∈ reads, issued read = true) :
    reads.find? (fun read => !(issued read && live read)) =
      reads.find? (fun read => !live read) := by
  induction reads with
  | nil => rfl
  | cons first rest ih =>
    have firstIssued := preflight first (by simp)
    have restIssued : ∀ read ∈ rest, issued read = true :=
      fun read member => preflight read (List.mem_cons_of_mem _ member)
    simp only [List.find?_cons, firstIssued, Bool.true_and, ih restIssued]

end LeanPoo.Object.CheckpointEntry

namespace LeanPoo.Object.NameCapture

/-- Contents of the producer's mutable name-cache spine and the record's
distinct public spine. They are separate native locations, even when equal. -/
structure Memory (Name : Type) where
  producer : List Name
  presented : List Name

inductive Seal (Name : Type) where
  | borrowedProducer
  | captured (names : List Name)

/-- A captured seal owns contents inaccessible through either mutable spine.
Native correspondence requires a detached copy held only by the birth closure. -/
def Verifies {Name : Type} (signature : Seal Name) (memory : Memory Name) : Prop :=
  match signature with
  | .borrowedProducer => memory.presented = memory.producer
  | .captured names => memory.presented = names

def overwriteBoth {Name : Type} (memory : Memory Name) (names : List Name) : Memory Name :=
  { memory with producer := names, presented := names }

/-- A producer-owned list is not a frozen birth snapshot: two ordinary heap
edits can make altered presentation and canonical alias agree again. -/
theorem borrowed_canonical_accepts_changed_payload {Name : Type}
    (original changed : List Name) (different : changed ≠ original) :
    Verifies (.borrowedProducer : Seal Name)
      (overwriteBoth ⟨original, original⟩ changed) ∧ changed ≠ original := ⟨rfl, different⟩

theorem owned_canonical_refuses_changed_payload {Name : Type}
    (original changed : List Name) (different : changed ≠ original) :
    ¬ Verifies (.captured original) (overwriteBoth ⟨original, original⟩ changed) := different

/-- The producer may subsequently change; issuance authentication remains
bound to the original snapshot. Actual receiver currentness is a SEPARATE check. -/
theorem producer_change_preserves_birth_contents {Name : Type}
    (original producer presented : List Name) :
    Verifies (.captured original) ⟨producer, presented⟩ ↔ presented = original := Iff.rfl

/-- Authentication is not a sticky refusal/success cache. Restoring the exact
original presentation restores its issuance; live route/state checks still run. -/
theorem restored_presentation_is_issued {Name : Type}
    (original producer : List Name) :
    Verifies (.captured original) ⟨producer, original⟩ := rfl

end LeanPoo.Object.NameCapture

/-! Revision admission for the EXISTING slot observation/value store. Snapshot
contents are ghost witnesses, not a second runtime table. Private reachability
and complete writer coverage are essential: the current public raw vector store
does NOT meet this frame merely because an epoch or a private flag is present. -/
namespace LeanPoo.Object.ReadRevision

structure Memory (Value : Type) where
  source : Nat
  generation : Nat
  values : Nat → Option Value
  exposed : Bool
  published : Nat → Bool
  /-- Ghost projection of version metadata in each existing cell, not a
  second native version table. Missing/deleted cells retain their tombstone. -/
  versions : Nat → Nat

structure Snapshot (Value : Type) where
  source : Nat
  generation : Nat
  values : Nat → Option Value
  versions : Nat → Nat

def allocate (source : Nat) (values : Nat → Option Value) : Memory Value :=
  ⟨source, 0, values, false, fun _ => false, fun _ => 0⟩

def snapshot (memory : Memory Value) : Snapshot Value :=
  ⟨memory.source, memory.generation, memory.values, memory.versions⟩

def Live (stamp : Snapshot Value) (memory : Memory Value) : Prop :=
  memory.source = stamp.source ∧ memory.generation = stamp.generation ∧ memory.exposed = false

/-- Reads only the authenticated source/generation/exposure header. A caller
must additionally establish Frame from real allocation/writer coverage. -/
def admit (stamp : Snapshot Value) (memory : Memory Value) : Bool :=
  decide (memory.source = stamp.source ∧ memory.generation = stamp.generation ∧ memory.exposed = false)

theorem admit_iff (stamp : Snapshot Value) (memory : Memory Value) :
    admit stamp memory = true ↔ Live stamp memory := by simp [admit, Live]

def Frame (stamp : Snapshot Value) (memory : Memory Value) : Prop :=
  memory.source = stamp.source ∧ stamp.generation ≤ memory.generation ∧
  (memory.exposed = false → ∀ key, memory.published key = false) ∧
  (Live stamp memory → memory.values = stamp.values)

def CellLive (stamp : Snapshot Value) (memory : Memory Value) (key : Nat) : Prop :=
  memory.source = stamp.source ∧ memory.versions key = stamp.versions key ∧ memory.exposed = false

def admitCell (stamp : Snapshot Value) (memory : Memory Value) (key : Nat) : Bool :=
  decide (memory.source = stamp.source ∧ memory.versions key = stamp.versions key ∧ memory.exposed = false)

/-- Versions belong to the same cells as values. This is the refinement needed
for unaffected slots to survive another slot's write; a whole-owner epoch alone
would discard all of them. -/
def CellFrame (stamp : Snapshot Value) (memory : Memory Value) : Prop :=
  (∀ key, memory.versions key ≤ memory.generation) ∧
  (∀ key, stamp.versions key ≤ memory.versions key) ∧
  (∀ key, CellLive stamp memory key → memory.values key = stamp.values key)

/-- Owner writes retire the previous generation even for the same value. -/
def put (memory : Memory Value) (key : Nat) (value : Option Value) : Memory Value :=
  { memory with generation := memory.generation + 1
                values := fun query => if query = key then value else memory.values query
                versions := fun query => if query = key then memory.generation + 1 else memory.versions query }

/-- Exposure precedes handoff. It refuses new constant-header admission; it
does not fabricate a write to already retained business values. -/
def expose (memory : Memory Value) (key : Nat) : Memory Value :=
  { memory with exposed := true
                published := fun query => if query = key then true else memory.published query }

/-- An ordinary raw writer need not notify the epoch. Its reference must have
escaped first; covering that handoff is the native correspondence obligation. -/
def rawPut (memory : Memory Value) (key : Nat) (value : Option Value) : Memory Value :=
  { memory with values := fun query => if query = key then value else memory.values query }

inductive Step : Memory Value → Memory Value → Prop where
  | put (memory key value) : Step memory (put memory key value)
  | expose (memory key) : Step memory (expose memory key)
  | raw (memory key value) (reference : memory.published key = true) :
      Step memory (rawPut memory key value)

inductive Reaches (start : Memory Value) : Memory Value → Prop where
  | refl : Reaches start start
  | next {before after} : Reaches start before → Step before after → Reaches start after

theorem allocated_frame (source : Nat) (values : Nat → Option Value) :
    Frame (snapshot (allocate source values)) (allocate source values) := by
  exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl, fun _ => rfl⟩

theorem step_frame {stamp : Snapshot Value} {before after : Memory Value}
    (valid : Frame stamp before) (step : Step before after) : Frame stamp after := by
  rcases valid with ⟨origin, lower, privateRefs, contents⟩
  cases step with
  | put key value =>
    refine ⟨origin, Nat.le_trans lower (Nat.le_succ _), privateRefs, ?_⟩
    intro accepted
    have same := accepted.2.1
    simp only [put] at same
    omega
  | expose key =>
    refine ⟨origin, lower, ?_, ?_⟩
    · intro closed
      simp [expose] at closed
    · intro accepted
      simp [Live, expose] at accepted
  | raw key value reference =>
    refine ⟨origin, lower, privateRefs, ?_⟩
    intro accepted
    have closed : before.exposed = false := accepted.2.2
    have absent := privateRefs closed key
    simp [reference] at absent

theorem reaches_frame {stamp : Snapshot Value} {before after : Memory Value}
    (valid : Frame stamp before) (path : Reaches before after) : Frame stamp after := by
  induction path with
  | refl => exact valid
  | next path step ih => exact step_frame ih step

/-- Reissue against the new authoritative generation; do not retain an old
ticket or physically copy a table merely to obtain this logical witness. -/
theorem renew_frame {stamp : Snapshot Value} (memory : Memory Value)
    (valid : Frame stamp memory) : Frame (snapshot memory) memory :=
  ⟨rfl, Nat.le_refl _, valid.2.2.1, fun _ => rfl⟩

theorem renewed_lookup_exact {stamp : Snapshot Value} {before after : Memory Value}
    (valid : Frame stamp before) (path : Reaches before after)
    (accepted : Live (snapshot before) after) (key : Nat) :
    after.values key = before.values key :=
  congrFun ((reaches_frame (renew_frame before valid) path).2.2.2 accepted) key

theorem admitted_frame_lookup {stamp : Snapshot Value} (memory : Memory Value)
    (valid : Frame stamp memory) (accepted : admit stamp memory = true) (key : Nat) :
    memory.values key = stamp.values key :=
  congrFun (valid.2.2.2 ((admit_iff stamp memory).mp accepted)) key

/-- Constant-header admission is exact ONLY over the derived covered domain.
The entire value map agrees, including missing entries and false/error values. -/
theorem admitted_values_exact (source : Nat) (values : Nat → Option Value)
    (after : Memory Value) (path : Reaches (allocate source values) after)
    (accepted : Live (snapshot (allocate source values)) after) : after.values = values :=
  (reaches_frame (allocated_frame source values) path).2.2.2 accepted

theorem admitted_lookup_exact (source : Nat) (values : Nat → Option Value)
    (after : Memory Value) (path : Reaches (allocate source values) after)
    (accepted : Live (snapshot (allocate source values)) after) (key : Nat) :
    after.values key = values key := congrFun (admitted_values_exact source values after path accepted) key

theorem exposure_refuses (stamp : Snapshot Value) (memory : Memory Value) (key : Nat) :
    ¬ Live stamp (expose memory key) := by simp [Live, expose]

theorem controlled_write_retires (memory : Memory Value) (key : Nat) (value : Option Value) :
    ¬ Live (snapshot memory) (put memory key value) := by
  simp [Live, snapshot, put]

theorem foreign_source_refuses (stamp : Snapshot Value) (memory : Memory Value)
    (different : memory.source ≠ stamp.source) : ¬ Live stamp memory :=
  fun accepted => different accepted.1

/-- A public uncooperative writer falsifies epoch-only validation. A caller's
private bit is insufficient; do not apply the covered-domain theorem to it. -/
theorem untracked_write_counterexample :
    let before := allocate 0 (fun _ => some false)
    let after := rawPut before 0 (some true)
    Live (snapshot before) after ∧ CellLive (snapshot before) after 0 ∧
      after.values 0 ≠ before.values 0 := by
  simp [allocate, rawPut, Live, CellLive, snapshot]

theorem allocated_cell_frame (source : Nat) (values : Nat → Option Value) :
    CellFrame (snapshot (allocate source values)) (allocate source values) := by
  exact ⟨fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, fun _ _ => rfl⟩

theorem step_cell_frame {stamp : Snapshot Value} {before after : Memory Value}
    (frame : Frame stamp before) (valid : CellFrame stamp before)
    (step : Step before after) : CellFrame stamp after := by
  rcases valid with ⟨bounded, monotone, contents⟩
  cases step with
  | put key value =>
    constructor
    · intro query
      by_cases same : query = key
      · simp [put, same]
      · simpa [put, same] using Nat.le_trans (bounded query) (Nat.le_succ before.generation)
    constructor
    · intro query
      by_cases same : query = key
      · simpa [put, same] using
          Nat.le_trans (monotone key) (Nat.le_trans (bounded key) (Nat.le_succ before.generation))
      · simpa [put, same] using monotone query
    · intro query accepted
      by_cases same : query = key
      · subst query
        have eqVersion : before.generation + 1 = stamp.versions key := by
          simpa [put] using accepted.2.1
        have stampBound := Nat.le_trans (monotone key) (bounded key)
        omega
      · have previous : CellLive stamp before query := by
          simpa [CellLive, put, same] using accepted
        simpa [put, same] using contents query previous
  | expose key =>
    refine ⟨bounded, monotone, ?_⟩
    intro query accepted
    simp [CellLive, expose] at accepted
  | raw key value reference =>
    refine ⟨bounded, monotone, ?_⟩
    intro query accepted
    have absent := frame.2.2.1 accepted.2.2 key
    simp [reference] at absent

theorem reaches_frames {stamp : Snapshot Value} {before after : Memory Value}
    (frame : Frame stamp before) (cells : CellFrame stamp before)
    (path : Reaches before after) : Frame stamp after ∧ CellFrame stamp after := by
  induction path with
  | refl => exact ⟨frame, cells⟩
  | next path step ih => exact ⟨step_frame ih.1 step, step_cell_frame ih.1 ih.2 step⟩

theorem admitted_cell_exact (source : Nat) (values : Nat → Option Value)
    (after : Memory Value) (path : Reaches (allocate source values) after) (key : Nat)
    (accepted : admitCell (snapshot (allocate source values)) after key = true) :
    after.values key = values key := by
  have live : CellLive (snapshot (allocate source values)) after key := by
    simpa [admitCell, CellLive] using accepted
  exact (reaches_frames (allocated_frame source values) (allocated_cell_frame source values) path).2.2.2 key live

theorem unaffected_cell_remains_live (memory : Memory Value) (changed watched : Nat)
    (value : Option Value) (different : watched ≠ changed) (private_ : memory.exposed = false) :
    CellLive (snapshot memory) (put memory changed value) watched ∧
      (put memory changed value).values watched = memory.values watched := by
  simp [CellLive, snapshot, put, different, private_]

theorem changed_cell_retires {stamp : Snapshot Value} (memory : Memory Value)
    (valid : CellFrame stamp memory) (key : Nat) (value : Option Value) :
    ¬ CellLive stamp (put memory key value) key := by
  intro accepted
  have same : memory.generation + 1 = stamp.versions key := by
    simpa [put] using accepted.2.1
  have lower := Nat.le_trans (valid.2.1 key) (valid.1 key)
  omega

theorem renew_cell_frame {stamp : Snapshot Value} (memory : Memory Value)
    (valid : CellFrame stamp memory) : CellFrame (snapshot memory) memory :=
  ⟨valid.1, fun _ => Nat.le_refl _, fun _ _ => rfl⟩

theorem renewed_cell_exact {stamp : Snapshot Value} {before after : Memory Value}
    (frame : Frame stamp before) (cells : CellFrame stamp before)
    (path : Reaches before after) (key : Nat)
    (accepted : CellLive (snapshot before) after key) :
    after.values key = before.values key :=
  (reaches_frames (renew_frame before frame) (renew_cell_frame before cells) path).2.2.2 key accepted

theorem step_versions_mono {stamp : Snapshot Value} {before after : Memory Value}
    (cells : CellFrame stamp before) (step : Step before after) (key : Nat) :
    before.versions key ≤ after.versions key := by
  cases step with
  | put changed value =>
    by_cases same : key = changed
    · simpa [put, same] using Nat.le_trans (cells.1 changed) (Nat.le_succ before.generation)
    · simp [put, same]
  | expose changed => exact Nat.le_refl _
  | raw changed value reference => exact Nat.le_refl _

theorem reaches_versions_mono {stamp : Snapshot Value} {before after : Memory Value}
    (frame : Frame stamp before) (cells : CellFrame stamp before)
    (path : Reaches before after) (key : Nat) : before.versions key ≤ after.versions key := by
  induction path with
  | refl => exact Nat.le_refl _
  | next path step ih =>
    exact Nat.le_trans ih (step_versions_mono (reaches_frames frame cells path).2 step key)

/-- Includes same-value writes and ABA: restoring the old payload cannot
restore its old observation ticket after any later covered transitions. -/
theorem changed_cell_stays_retired {stamp : Snapshot Value} (memory after : Memory Value)
    (frame : Frame stamp memory) (cells : CellFrame stamp memory)
    (key : Nat) (value : Option Value) (path : Reaches (put memory key value) after) :
    ¬ CellLive stamp after key := by
  intro accepted
  have firstFrame := step_frame frame (Step.put memory key value)
  have firstCells := step_cell_frame frame cells (Step.put memory key value)
  have later := reaches_versions_mono firstFrame firstCells path key
  have grew : memory.generation + 1 ≤ after.versions key := by simpa [put] using later
  have old := Nat.le_trans (cells.2.1 key) (cells.1 key)
  have same := accepted.2.1
  omega

theorem step_exposure_stays {before after : Memory Value} (step : Step before after)
    (exposed : before.exposed = true) : after.exposed = true := by
  cases step <;> simp_all [put, expose, rawPut]

theorem reaches_exposure_stays {before after : Memory Value} (path : Reaches before after)
    (exposed : before.exposed = true) : after.exposed = true := by
  induction path with
  | refl => exact exposed
  | next path step ih => exact step_exposure_stays step ih

theorem exposed_cell_stays_refused (stamp : Snapshot Value) (memory after : Memory Value)
    (exposed : memory.exposed = true) (path : Reaches memory after) (key : Nat) :
    ¬ CellLive stamp after key := by
  intro accepted
  have committed := reaches_exposure_stays path exposed
  have closed := accepted.2.2
  simp [committed] at closed

end LeanPoo.Object.ReadRevision

namespace LeanPoo.Object.PublishedRead

/-- One existing signing index may contain distinct issuer domains and owned
metadata. Scope/kind are private identity capabilities in Scheme, not hashes. -/
inductive Kind where
  | read | owned
  deriving DecidableEq

structure Binding (Data : Type) where
  scope : Nat
  kind : Kind
  data : Data

abbrev Store (Data : Type) := Nat → Option (Binding Data)

/-- Raw construction never grants a signing identity. Published references
are opaque token identities; the actual token retains its sole private payload. -/
inductive Reference (Data : Type) where
  | raw (data : Data)
  | published (token : Nat)

def authenticate (store : Store Data) (scope : Nat) (kind : Kind) :
    Reference Data → Option Data
  | .raw _ => none
  | .published token => do
    let binding ← store token
    if binding.scope = scope ∧ binding.kind = kind then some binding.data else none

/-- The supported signing operation inserts fresh identities; no successful
operation can replace the payload of an already published live token. -/
def publish (store : Store Data) (token : Nat) (binding : Binding Data) :
    Option (Store Data) :=
  match store token with
  | some _ => none
  | none => some (fun key => if key = token then some binding else store key)

def Extends (before after : Store Data) : Prop :=
  ∀ token binding, before token = some binding → after token = some binding

theorem publish_extends (store : Store Data) (token : Nat) (binding : Binding Data)
    (after : Store Data) (success : publish store token binding = some after) :
    Extends store after := by
  unfold publish at success
  split at success
  · contradiction
  · cases success
    intro key old present
    by_cases same : key = token
    · subst key; simp_all
    · simp [same, present]

theorem published_payload_fixed (before after : Store Data) (scope : Nat) (kind : Kind)
    (reference : Reference Data) (data : Data) (appendOnly : Extends before after)
    (accepted : authenticate before scope kind reference = some data) :
    authenticate after scope kind reference = some data := by
  cases reference with
  | raw _ => simp [authenticate] at accepted
  | published token =>
    cases found : before token with
    | none => simp [authenticate, found] at accepted
    | some binding =>
      have preserved := appendOnly token binding found
      simpa [authenticate, found, preserved] using accepted

theorem raw_never_issued (store : Store Data) (scope : Nat) (kind : Kind) (data : Data) :
    authenticate store scope kind (.raw data) = none := rfl

theorem foreign_scope_refused (store : Store Data) (scope token : Nat)
    (kind : Kind) (binding : Binding Data) (found : store token = some binding)
    (foreign : binding.scope ≠ scope) :
    authenticate store scope kind (.published token) = none := by
  simp [authenticate, found, foreign]

theorem foreign_kind_refused (store : Store Data) (scope token : Nat)
    (kind : Kind) (binding : Binding Data) (found : store token = some binding)
    (foreign : binding.kind ≠ kind) :
    authenticate store scope kind (.published token) = none := by
  simp [authenticate, found, foreign]

/-- Public snapshot edits have their own storage; the signing index is NOT a
mutable presentation. Snapshot copying and non-aliasing are native obligations. -/
structure Exposed (Data View : Type) where
  store : Store Data
  snapshots : Nat → Option View

def writeSnapshot (world : Exposed Data View) (address : Nat) (view : View) :
    Exposed Data View :=
  { world with snapshots := fun key => if key = address then some view else world.snapshots key }

theorem snapshot_write_preserves_issuance (world : Exposed Data View) (address : Nat)
    (view : View) (scope : Nat) (kind : Kind) (reference : Reference Data) :
    authenticate (writeSnapshot world address view).store scope kind reference =
      authenticate world.store scope kind reference := rfl

/-- There are no public metadata fields on the opaque published token.
Unsupported MOP writes refuse rather than editing a second presentation. -/
def writeMetadata (reference : Reference Data) (edit : Data → Data) : Option (Reference Data) :=
  match reference with
  | .raw data => some (.raw (edit data))
  | .published _ => none

theorem published_write_refused (token : Nat) (edit : Data → Data) :
    writeMetadata (.published token) edit = none := rfl

inductive Refusal where
  | unissued | route | revision | slot
  deriving DecidableEq

/-- Fixed issuance does not certify CURRENT receiver routing, revision or Slot
state. Every boundary re-enters this operation in its actual current world. -/
def admit (store : Store Data) (scope : Nat) (reference : Reference Data)
    (route revision slot : World → Data → Bool) (world : World) : Except Refusal Data :=
  match authenticate store scope .read reference with
  | none => .error .unissued
  | some data => if !route world data then .error .route else
      if !revision world data then .error .revision else
      if !slot world data then .error .slot else .ok data

theorem refusal_order (store : Store Data) (scope : Nat) (reference : Reference Data)
    (route revision slot : World → Data → Bool) (world : World)
    (missing : authenticate store scope .read reference = none) :
    admit store scope reference route revision slot world = .error .unissued := by
  simp [admit, missing]

theorem callback_revision_refused (store : Store Data) (scope : Nat)
    (reference : Reference Data) (data : Data) (route revision slot : World → Data → Bool)
    (after : World) (issued : authenticate store scope .read reference = some data)
    (routing : route after data = true) (changed : revision after data = false) :
    admit store scope reference route revision slot after = .error .revision := by
  simp [admit, issued, routing, changed]

theorem callback_slot_refused (store : Store Data) (scope : Nat)
    (reference : Reference Data) (data : Data) (route revision slot : World → Data → Bool)
    (after : World) (issued : authenticate store scope .read reference = some data)
    (routing : route after data = true) (current : revision after data = true)
    (changed : slot after data = false) :
    admit store scope reference route revision slot after = .error .slot := by
  simp [admit, issued, routing, current, changed]

/-- Reference replay repeats issuance before each live decision. The two later
stores model internal append-only publication, not arbitrary callback effects. -/
def repeatedAdmission (first second third : Store Data) (scope : Nat)
    (reference : Reference Data) (route revision slot : World → Data → Bool)
    (world : World) : Except Refusal Data :=
  match authenticate first scope .read reference with
  | none => .error .unissued
  | some data => if !route world data then .error .route else
      match authenticate second scope .read reference with
      | none => .error .unissued
      | some secondData => if !revision world secondData then .error .revision else
          match authenticate third scope .read reference with
          | none => .error .unissued
          | some thirdData => if !slot world thirdData then .error .slot else .ok thirdData

/-- Sharing issuance does not share any live decision: route, revision and Slot
still run in the original refusal order against this interval's current world.
No callback or concurrent write is licensed by Extends. -/
theorem shared_issuance_equals_repeated (first second third : Store Data)
    (scope : Nat) (reference : Reference Data)
    (route revision slot : World → Data → Bool) (world : World)
    (secondFixed : Extends first second) (thirdFixed : Extends first third) :
    repeatedAdmission first second third scope reference route revision slot world =
      admit first scope reference route revision slot world := by
  cases issued : authenticate first scope .read reference with
  | none => simp [repeatedAdmission, admit, issued]
  | some data =>
    have secondIssued := published_payload_fixed first second scope .read reference
      data secondFixed issued
    have thirdIssued := published_payload_fixed first third scope .read reference
      data thirdFixed issued
    simp [repeatedAdmission, admit, issued, secondIssued, thirdIssued]

/-- Only this already accepted reference must retain its binding. Unrelated
weak rows may disappear; a global append-only-store invariant is unnecessary. -/
def StableIssuance (before after : Store Data) (scope : Nat)
    (reference : Reference Data) : Prop :=
  ∀ data, authenticate before scope .read reference = some data →
    authenticate after scope .read reference = some data

theorem shared_issuance_equals_framed (first second third : Store Data)
    (scope : Nat) (reference : Reference Data)
    (route revision slot : World → Data → Bool) (world : World)
    (secondFixed : StableIssuance first second scope reference)
    (thirdFixed : StableIssuance first third scope reference) :
    repeatedAdmission first second third scope reference route revision slot world =
      admit first scope reference route revision slot world := by
  cases issued : authenticate first scope .read reference with
  | none => simp [repeatedAdmission, admit, issued]
  | some data =>
    have secondIssued := secondFixed data issued
    have thirdIssued := thirdFixed data issued
    simp [repeatedAdmission, admit, issued, secondIssued, thirdIssued]

/-- Weak association is not a global lifetime root. A live token's closure
must retain its payload; dead keys are discarded even if a payload stays live. -/
def collect (store : Store Data) (tokenLive payloadLive : Nat → Bool) : Store Data :=
  fun token => if tokenLive token && payloadLive token then store token else none

theorem live_token_keeps_payload (store : Store Data) (tokenLive payloadLive : Nat → Bool)
    (captured : ∀ token, tokenLive token = true → payloadLive token = true)
    (token : Nat) (live : tokenLive token = true) :
    collect store tokenLive payloadLive token = store token := by
  simp [collect, live, captured token live]

/-- Native replay retains its input token and that token's sole payload. Weak
collection of unrelated rows cannot invalidate this accepted read. -/
theorem live_collection_preserves_issuance (store : Store Data)
    (tokenLive payloadLive : Nat → Bool)
    (captured : ∀ token, tokenLive token = true → payloadLive token = true)
    (scope token : Nat) (live : tokenLive token = true) :
    StableIssuance store (collect store tokenLive payloadLive) scope (.published token) := by
  intro data accepted
  have kept := live_token_keeps_payload store tokenLive payloadLive captured token live
  simpa [authenticate, kept] using accepted

theorem dead_token_drops_index_row (store : Store Data) (tokenLive payloadLive : Nat → Bool)
    (token : Nat) (dead : tokenLive token = false) :
    collect store tokenLive payloadLive token = none := by simp [collect, dead]

#print axioms publish_extends
#print axioms published_payload_fixed
#print axioms shared_issuance_equals_framed
#print axioms live_collection_preserves_issuance
#print axioms shared_issuance_equals_repeated
#print axioms snapshot_write_preserves_issuance
#print axioms callback_slot_refused
end LeanPoo.Object.PublishedRead
