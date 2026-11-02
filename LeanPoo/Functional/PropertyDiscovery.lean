import LeanPoo.Functional.PropertyScopes

/-! Finite metadata directories and first-observation revision ownership.
Host shape normalization, shallow copies, primitive revision reads and terminating
sequential callbacks remain premises; no runtime or compiler proof is claimed. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Read one finite Function declaration row under the already captured epochs,
then retain newly discovered clause/input identities. No child generator is run.
The host supplies faithful terminating metadata reads and revision counters. -/
def observeFunctionInputs [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat))
    (read : State → Except Cause (List Source × State)) (state : State) :
    Except (Option Cause) (List Source × (State × List (Source × Nat))) :=
  (guardedGeneration (fun before => revisionsCurrent (current before) ledger) read state).map
    (fun result => (result.1, (result.2, captureSources (current result.2) ledger result.1)))

/-- A stale Function/clause/input skips the next getter, not merely child draws. -/
theorem observeFunctionInputs_stale [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (List Source × State)) (state : State)
    (stale : revisionsCurrent (current state) ledger = false) :
    observeFunctionInputs current ledger read state = .error none := by
  simp [observeFunctionInputs, guardedGeneration_preflight (fun before => revisionsCurrent (current before) ledger) read state stale, Except.map]

/-- A computed field cannot retire a known participant and capture its new epoch. -/
theorem observeFunctionInputs_revised [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state next : State) (row : List Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = false) :
    observeFunctionInputs (Cause := Cause) current ledger (fun _ => .ok (row, next)) state = .error none := by
  simp [observeFunctionInputs, guardedGeneration_revised (fun before => revisionsCurrent (current before) ledger) state next row before after, Except.map]

/-- Original metadata errors, including false, retain precedence over retirement. -/
theorem observeFunctionInputs_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state : State) (cause : Cause)
    (before : revisionsCurrent (current state) ledger = true) :
    observeFunctionInputs current ledger (fun _ => .error cause) state = .error (some cause) := by
  simp [observeFunctionInputs, guardedGeneration_cause (fun before => revisionsCurrent (current before) ledger) state cause before, Except.map]

/-- Stable discovery preserves exact row order and records each first observation. -/
theorem observeFunctionInputs_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state next : State) (row : List Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) :
    observeFunctionInputs (Cause := Cause) current ledger (fun _ => .ok (row, next)) state =
      .ok (row, (next, captureSources (current next) ledger row)) := by
  simp [observeFunctionInputs, guardedGeneration_state (fun before => revisionsCurrent (current before) ledger) state next row before after, Except.map]

/-- A later metadata field cannot repair retirement by rediscovering declarations.
This applies equally to a cached layout or an unforced optional child. -/
theorem functionInputs_retained_refusal [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source) (state : State)
    (draw : State → Except Cause (Value × State))
    (stale : revisionsCurrent (current state) ledger = false) :
    guardedGeneration (fun before => revisionsCurrent (current before)
      (captureSources (current state) ledger row)) draw state = .error none := by
  exact guardedGeneration_preflight _ draw state (captureSources_stale _ row ledger stale)

/-- Captured metadata bookkeeping is bounded by returned identities, not trials
or cached-layout hits. This is a ledger-size bound, not a runtime latency claim. -/
theorem functionInputs_capture_cost [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source) :
    (captureSources current ledger row).length ≤ ledger.length + row.length :=
  captureSources_cost current row ledger

/-- Repeated known declarations do not refresh epochs even if callbacks advanced
state; only explicit fresh preparation can establish a new initial ledger. -/
theorem functionInputs_known [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source)
    (known : ∀ source ∈ row, source ∈ ledger.map Prod.fst) :
    captureSources current ledger row = ledger := captureSources_known current row ledger known

/-- Refused metadata acquisition cannot enter subsequent generator construction. -/
theorem observeFunctionInputs_refused [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (List Source × State))
    (state : State) (cause : Option Cause)
    (build : List Source × (State × List (Source × Nat)) → Except (Option Cause) Value)
    (refused : observeFunctionInputs current ledger read state = .error cause) :
    (observeFunctionInputs current ledger read state >>= build) = .error cause := by
  rw [refused]; rfl

/-- A fixed carrier edge spends occurrence fuel before its metadata callback,
then records the returned Type at first observation. Shared IDs still spend fuel.
Host callbacks terminate and source revisions faithfully describe supported edits. -/
def discoverCarrierEdge [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat)
    (read : State → Except Cause (Source × State)) (state : State) :
    Except (Option Cause) (Source × (State × Nat × List (Source × Nat))) :=
  match fuel with
  | 0 => .error (some quota)
  | rest + 1 =>
    (guardedGeneration (fun before => revisionsCurrent (current before) ledger) read state).map
      (fun result => (result.1, (result.2, rest,
        captureRevision ledger result.1 (current result.2 result.1))))

/-- Exhausted discovery never evaluates a computed child declaration. -/
theorem discoverCarrierEdge_empty [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause)
    (read : State → Except Cause (Source × State)) (state : State) :
    discoverCarrierEdge current ledger quota 0 read state = .error (some quota) := rfl

/-- Available fuel does not authorize a getter under obsolete captured epochs. -/
theorem discoverCarrierEdge_stale [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat)
    (read : State → Except Cause (Source × State)) (state : State)
    (stale : revisionsCurrent (current state) ledger = false) :
    discoverCarrierEdge current ledger quota (fuel + 1) read state = .error none := by
  simp [discoverCarrierEdge, guardedGeneration_preflight
    (fun before => revisionsCurrent (current before) ledger) read state stale, Except.map]

/-- Original exceptions, including false, bypass normal post-return refusal. -/
theorem discoverCarrierEdge_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota cause : Cause) (fuel : Nat) (state : State)
    (before : revisionsCurrent (current state) ledger = true) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .error cause) state =
      .error (some cause) := by
  simp [discoverCarrierEdge, guardedGeneration_cause
    (fun before => revisionsCurrent (current before) ledger) state cause before, Except.map]

/-- A later Pair field cannot retire its earlier captured sibling and publish. -/
theorem discoverCarrierEdge_revised [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = false) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state = .error none := by
  simp [discoverCarrierEdge, guardedGeneration_revised
    (fun before => revisionsCurrent (current before) ledger) state next child before after, Except.map]

/-- Stable discovery returns the exact child, actual state and one fewer edge. -/
theorem discoverCarrierEdge_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state =
      .ok (child, (next, fuel, captureRevision ledger child (current next child))) := by
  simp [discoverCarrierEdge, guardedGeneration_state
    (fun before => revisionsCurrent (current before) ledger) state next child before after, Except.map]

/-- Shared child occurrences spend edge fuel without refreshing the old epoch. -/
theorem discoverCarrierEdge_shared [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) (known : child ∈ ledger.map Prod.fst) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state =
      .ok (child, (next, fuel, ledger)) := by
  rw [discoverCarrierEdge_stable current ledger quota fuel state next child before after,
    captureRevision_existing ledger child (current next child) known]

/-- Capturing a child makes it current for the next field while retaining all
prior authority; it never validates the child's generator or recursive payload. -/
theorem discoverCarrierEdge_current [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (child : Source) (before : revisionsCurrent current ledger = true) :
    revisionsCurrent current (captureRevision ledger child (current child)) = true :=
  captureRevision_fresh current ledger child before

/-- Registration grows by at most one identity per edge, independently of sharing.
This bounds ledger cardinality, not callback runtime or hash-table latency. -/
theorem discoverCarrierEdge_capture_cost [DecidableEq Source] (ledger : List (Source × Nat))
    (child : Source) (epoch : Nat) :
    (captureRevision ledger child epoch).length ≤ ledger.length + 1 :=
  captureRevision_length ledger child epoch

/-- Admit a complete known directory before copying or child callbacks. Shared
occurrences spend width budget, while existing captureSources deduplicates epochs.
The consumer is the existing ordered edge traversal, not a second visitor. -/
def prepareCarrierDirectory [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat)
    (input : Option (List Source))
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output) :
    Except (Option Cause) Output :=
  match input with
  | none => .error (some invalid)
  | some row => if row.length ≤ fuel then consume row (captureSources clock ledger row)
      else .error (some quota)

/-- Improper/cyclic host directories cannot enter any child traversal. -/
theorem prepareCarrierDirectory_malformed [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat)
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output) :
    prepareCarrierDirectory clock ledger invalid quota fuel none consume = .error (some invalid) := rfl

/-- A complete row exceeding remaining occurrence fuel skips every consumer. -/
theorem prepareCarrierDirectory_quota [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat) (row : List Source)
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output)
    (large : fuel < row.length) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some row) consume = .error (some quota) := by
  simp [prepareCarrierDirectory, Nat.not_le.mpr large]

/-- An admitted row retains its exact order and captures all known epochs first. -/
theorem prepareCarrierDirectory_admitted [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat) (row : List Source)
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output)
    (fits : row.length ≤ fuel) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some row) consume =
      consume row (captureSources clock ledger row) := by simp [prepareCarrierDirectory, fits]

/-- Present empty rows are legal at zero fuel and add no child observations. -/
theorem prepareCarrierDirectory_empty [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat)
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some []) consume = consume [] ledger := by
  simp [prepareCarrierDirectory, captureSources]

/-- Repeated known identities keep old epochs rather than renewing authority. -/
theorem prepareCarrierDirectory_known [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat) (row : List Source)
    (consume : List Source → List (Source × Nat) → Except (Option Cause) Output)
    (fits : row.length ≤ fuel) (known : ∀ source ∈ row, source ∈ ledger.map Prod.fst) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some row) consume = consume row ledger := by
  rw [prepareCarrierDirectory_admitted clock ledger invalid quota fuel row consume fits,
    captureSources_known clock row ledger known]

/-- Successful capture preserves the full input, bounds copied width by remaining
fuel, and adds at most one source entry per occurrence. This is not RSS or time. -/
theorem prepareCarrierDirectory_bounds [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid quota : Cause) (fuel : Nat)
    (input : Option (List Source)) (result : List Source × List (Source × Nat))
    (prepared : prepareCarrierDirectory clock ledger invalid quota fuel input
      (fun row owned => .ok (row, owned)) = .ok result) :
    input = some result.1 ∧ result.1.length ≤ fuel ∧ result.2.length ≤ ledger.length + result.1.length := by
  cases input with
  | none => simp [prepareCarrierDirectory] at prepared
  | some row =>
    dsimp only [prepareCarrierDirectory] at prepared
    split at prepared
    · rename_i fits
      have same := Except.ok.inj prepared
      subst result
      exact ⟨rfl, fits, captureSources_cost clock row ledger⟩
    · cases prepared

/-- The existing edge gate refuses a revised known sibling before its getter. -/
theorem prepareCarrierDirectory_edge_stale [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid quota : Cause)
    (fuel edgeFuel : Nat) (row : List Source) (read : State → Except Cause (Source × State))
    (state : State) (fits : row.length ≤ fuel)
    (stale : revisionsCurrent (current state) (captureSources clock ledger row) = false) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some row)
      (fun _ owned => discoverCarrierEdge current owned quota (edgeFuel + 1) read state) = .error none := by
  rw [prepareCarrierDirectory_admitted _ _ _ _ _ _ _ fits]
  exact discoverCarrierEdge_stale current _ quota edgeFuel read state stale

/-- A live directory retains an original edge callback cause, including false. -/
theorem prepareCarrierDirectory_edge_cause [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid quota cause : Cause)
    (fuel edgeFuel : Nat) (row : List Source) (state : State) (fits : row.length ≤ fuel)
    (fresh : revisionsCurrent (current state) (captureSources clock ledger row) = true) :
    prepareCarrierDirectory clock ledger invalid quota fuel (some row)
      (fun _ owned => discoverCarrierEdge current owned quota (edgeFuel + 1) (fun _ => .error cause) state) =
      .error (some cause) := by
  rw [prepareCarrierDirectory_admitted _ _ _ _ _ _ _ fits]
  exact discoverCarrierEdge_cause current _ quota cause edgeFuel state fresh

/-- Directory preparation cannot repair an obsolete incoming ledger by recapture. -/
theorem prepareCarrierDirectory_prior_stale [DecidableEq Source]
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid quota : Cause)
    (fuel edgeFuel : Nat) (row : List Source) (read : State → Except Cause (Source × State))
    (state : State) (fits : row.length ≤ fuel) (stale : revisionsCurrent (current state) ledger = false) :
    prepareCarrierDirectory (current state) ledger invalid quota fuel (some row)
      (fun _ owned => discoverCarrierEdge current owned quota (edgeFuel + 1) read state) = .error none := by
  exact prepareCarrierDirectory_edge_stale (current state) current ledger invalid quota fuel edgeFuel row
    read state fits (captureSources_stale (current state) row ledger stale)

/-- Own a finite Sum tag row and the returned directory epoch before the next
source observer. None represents host grammar refusal (shape, symbol or duplicate).
The clock is sampled at getter return; observe models the following checked action.
Payload getters remain the existing discoverCarrierEdge operation. -/
def observeVariantDirectory [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat) (input : Option (List Tag))
    (observe : State → Except Cause (Value × State)) (state : State) :
    Except (Option Cause) (List Tag × (Value × State) × List (Source × Nat)) :=
  match input with
  | none => .error (some invalid)
  | some tags => if tags.length ≤ fuel then
      let owned := captureRevision ledger directory (clock directory)
      (guardedGeneration (fun now => revisionsCurrent (current now) owned) observe state).map
        (fun result => (tags, result, owned))
    else .error (some quota)

/-- Invalid tag grammar keeps precedence and skips source observers and payloads. -/
theorem observeVariantDirectory_invalid [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat)
    (observe : State → Except Cause (Value × State)) (state : State) :
    observeVariantDirectory (Tag := Tag) clock current ledger directory invalid quota fuel none observe state =
      .error (some invalid) := rfl

/-- Complete occurrence width refuses before any returning observer or payload. -/
theorem observeVariantDirectory_quota [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat) (tags : List Tag)
    (observe : State → Except Cause (Value × State)) (state : State) (large : fuel < tags.length) :
    observeVariantDirectory clock current ledger directory invalid quota fuel (some tags) observe state =
      .error (some quota) := by simp [observeVariantDirectory, Nat.not_le.mpr large]

/-- A directory already retired before observation cannot enter its next action. -/
theorem observeVariantDirectory_stale [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat) (tags : List Tag)
    (observe : State → Except Cause (Value × State)) (state : State) (fits : tags.length ≤ fuel)
    (stale : revisionsCurrent (current state) (captureRevision ledger directory (clock directory)) = false) :
    observeVariantDirectory clock current ledger directory invalid quota fuel (some tags) observe state =
      .error none := by
  simp [observeVariantDirectory, fits, guardedGeneration_preflight (fun now => revisionsCurrent (current now) (captureRevision ledger directory (clock directory))) observe state stale, Except.map]

/-- Revising the captured directory during observation refuses normal publication. -/
theorem observeVariantDirectory_revised [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat) (tags : List Tag) (value : Value) (state next : State)
    (fits : tags.length ≤ fuel)
    (before : revisionsCurrent (current state) (captureRevision ledger directory (clock directory)) = true)
    (after : revisionsCurrent (current next) (captureRevision ledger directory (clock directory)) = false) :
    observeVariantDirectory clock current ledger directory invalid quota fuel (some tags)
      (fun _ => .ok (value, next)) state = .error none := by
  simp [observeVariantDirectory, fits, guardedGeneration_revised (fun now => revisionsCurrent (current now) (captureRevision ledger directory (clock directory))) state next value before after, Except.map]

/-- A live observer's original cause survives, including a thrown false value. -/
theorem observeVariantDirectory_cause [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota cause : Cause) (fuel : Nat) (tags : List Tag) (state : State) (fits : tags.length ≤ fuel)
    (before : revisionsCurrent (current state) (captureRevision ledger directory (clock directory)) = true) :
    observeVariantDirectory (Value := Value) clock current ledger directory invalid quota fuel (some tags)
      (fun _ => .error cause) state = .error (some cause) := by
  simp [observeVariantDirectory, fits, guardedGeneration_cause (fun now => revisionsCurrent (current now) (captureRevision ledger directory (clock directory))) state cause before, Except.map]

/-- Successful observation retains original labels/order rather than an observer's
mutable list spelling. Host shallow-copy fidelity is an explicit premise. -/
theorem observeVariantDirectory_retained [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (directory : Source)
    (invalid quota : Cause) (fuel : Nat) (tags : List Tag) (value : Value) (state next : State)
    (fits : tags.length ≤ fuel)
    (before : revisionsCurrent (current state) (captureRevision ledger directory (clock directory)) = true)
    (after : revisionsCurrent (current next) (captureRevision ledger directory (clock directory)) = true) :
    observeVariantDirectory clock current ledger directory invalid quota fuel (some tags)
      (fun _ => .ok (value, next)) state =
      .ok (tags, (value, next), captureRevision ledger directory (clock directory)) := by
  simp [observeVariantDirectory, fits, guardedGeneration_state (fun now => revisionsCurrent (current now) (captureRevision ledger directory (clock directory))) state next value before after, Except.map]

/-- Capturing an already known directory never renews its epoch. -/
theorem variantDirectory_known [DecidableEq Source] (ledger : List (Source × Nat))
    (directory : Source) (epoch : Nat) (known : directory ∈ ledger.map Prod.fst) :
    captureRevision ledger directory epoch = ledger := captureRevision_existing ledger directory epoch known

/-- The extra Sum participant costs at most one ledger entry, independently of
shared payload count; copied tag width is admitted separately by occurrence fuel. -/
theorem variantDirectory_capture_cost [DecidableEq Source] (ledger : List (Source × Nat))
    (directory : Source) (epoch : Nat) :
    (captureRevision ledger directory epoch).length ≤ ledger.length + 1 :=
  captureRevision_length ledger directory epoch

/-- First-return ownership of a sampler declaration row, before the returning
observer. A singleton models descriptor/bound-descriptor; finite rows model sources.
The getter has already returned: clock and row are captured at that boundary.
Host proper-list normalization, pure capture and shallow-copy fidelity are premises. -/
def observeCapturedSources [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (input : Option (List Source)) (observe : State → Except Cause (Value × State)) (state : State) :
    Except (Option Cause) (List Source × (Value × State) × List (Source × Nat)) :=
  match input with
  | none => .error (some invalid)
  | some row =>
    let owned := captureSources clock ledger row
    (guardedGeneration (fun now => revisionsCurrent (current now) owned) observe state).map
      (fun result => (row, result, owned))

/-- Malformed dependencies cannot enter the returning observer or later binding. -/
theorem observeCapturedSources_invalid [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (observe : State → Except Cause (Value × State)) (state : State) :
    observeCapturedSources clock current ledger invalid none observe state = .error (some invalid) := rfl

/-- Captured retirement suppresses subsequent observer/binder effects. -/
theorem observeCapturedSources_stale [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (row : List Source) (observe : State → Except Cause (Value × State)) (state : State)
    (stale : revisionsCurrent (current state) (captureSources clock ledger row) = false) :
    observeCapturedSources clock current ledger invalid (some row) observe state = .error none := by
  simp [observeCapturedSources, guardedGeneration_preflight
    (fun now => revisionsCurrent (current now) (captureSources clock ledger row)) observe state stale, Except.map]

/-- A returning observer cannot retire a newly returned participant then publish it. -/
theorem observeCapturedSources_revised [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (row : List Source) (state next : State) (value : Value)
    (before : revisionsCurrent (current state) (captureSources clock ledger row) = true)
    (after : revisionsCurrent (current next) (captureSources clock ledger row) = false) :
    observeCapturedSources clock current ledger invalid (some row) (fun _ => .ok (value, next)) state =
      .error none := by
  simp [observeCapturedSources, guardedGeneration_revised
    (fun now => revisionsCurrent (current now) (captureSources clock ledger row)) state next value before after, Except.map]

/-- Accepted observation retains the complete original row, order and duplicates. -/
theorem observeCapturedSources_retained [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (row : List Source) (state next : State) (value : Value)
    (before : revisionsCurrent (current state) (captureSources clock ledger row) = true)
    (after : revisionsCurrent (current next) (captureSources clock ledger row) = true) :
    observeCapturedSources clock current ledger invalid (some row) (fun _ => .ok (value, next)) state =
      .ok (row, (value, next), captureSources clock ledger row) := by
  simp [observeCapturedSources, guardedGeneration_state
    (fun now => revisionsCurrent (current now) (captureSources clock ledger row)) state next value before after, Except.map]

/-- Original observer causes bypass trailing freshness checks unchanged. -/
theorem observeCapturedSources_cause [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid cause : Cause)
    (row : List Source) (state : State)
    (before : revisionsCurrent (current state) (captureSources clock ledger row) = true) :
    observeCapturedSources (Value := Value) clock current ledger invalid (some row)
      (fun _ => .error cause) state = .error (some cause) := by
  simp [observeCapturedSources, guardedGeneration_cause
    (fun now => revisionsCurrent (current now) (captureSources clock ledger row)) state cause before, Except.map]

/-- New declarations cannot refresh an already stale owner captured by an outer run. -/
theorem observeCapturedSources_prior_stale [DecidableEq Source] (clock : Source → Nat)
    (ledger : List (Source × Nat)) (invalid : Cause) (row : List Source)
    (observe : State → Except Cause (Value × State)) (state : State)
    (current : State → Source → Nat) (same : current state = clock)
    (stale : revisionsCurrent clock ledger = false) :
    observeCapturedSources clock current ledger invalid (some row) observe state = .error none := by
  apply observeCapturedSources_stale
  rw [same]
  exact captureSources_stale clock row ledger stale

/-- Refusal cannot enter a dependent generator factory or replay binder. -/
theorem observeCapturedSources_refused [DecidableEq Source] (clock : Source → Nat)
    (current : State → Source → Nat) (ledger : List (Source × Nat)) (invalid : Cause)
    (input : Option (List Source)) (observe : State → Except Cause (Value × State)) (state : State)
    (bind : List Source × (Value × State) × List (Source × Nat) → Except (Option Cause) Output)
    (cause : Option Cause)
    (refused : observeCapturedSources clock current ledger invalid input observe state = .error cause) :
    (observeCapturedSources clock current ledger invalid input observe state >>= bind) = .error cause := by
  rw [refused]; rfl

end LeanPoo.Functional.PropertyTesting
