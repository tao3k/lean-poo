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

