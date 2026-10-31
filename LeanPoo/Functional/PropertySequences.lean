import LeanPoo.Functional.PropertyGenerators

/-! Finite sequence preparation. Malformed host spines are represented by none;
accurate shape conversion, source observers and terminating callbacks are premises.
The general lazy Iterator protocol is deliberately not constrained here. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Reject malformed spines before entering model/candidate preparation. Empty
proper lists remain present data and retain their ordinary preparation behavior. -/
def finiteSequenceInput (invalid : Cause) (input : Option (List Value))
    (prepare : List Value → Except (Option Cause) Output) : Except (Option Cause) Output :=
  match input with
  | none => .error (some invalid)
  | some values => prepare values

/-- A parameter callback first satisfies the existing source boundary, then its
returned finite shape. Source revision therefore precedes normal-result admission;
original callback exceptions retain their cause. No partial batch is published. -/
def finiteShrinkStage (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) : Except (Option Cause) (List Output × State) :=
  match guardedGeneration live (shrink value) state with
  | .error cause => .error cause
  | .ok (none, _) => .error (some invalid)
  | .ok (some values, next) => .ok (values, next)

/-- No initializer or candidate repair is reachable after malformed input. -/
theorem finiteSequenceInput_refused (invalid : Cause)
    (prepare : List Value → Except (Option Cause) Output) :
    finiteSequenceInput invalid none prepare = .error (some invalid) := rfl

/-- A proper input is forwarded exactly, including an empty list. -/
theorem finiteSequenceInput_present (invalid : Cause) (values : List Value)
    (prepare : List Value → Except (Option Cause) Output) :
    finiteSequenceInput invalid (some values) prepare = prepare values := rfl

/-- Already obsolete preparation cannot invoke its parameter callback. -/
theorem finiteShrinkStage_stale (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) (stale : live state = false) :
    finiteShrinkStage live invalid shrink value state = .error none := by
  simp [finiteShrinkStage, guardedGeneration, stale]

/-- Normal callback revision skips shape admission and the next coordinate. -/
theorem finiteShrinkStage_revised (live : State → Bool) (invalid : Cause)
    (values : Option (List Output)) (value : Value) (state next : State)
    (before : live state = true) (after : live next = false) :
    finiteShrinkStage live invalid (fun _ _ => .ok (values, next)) value state = .error none := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Callback exceptions remain exact even when normal-result checks would fail. -/
theorem finiteShrinkStage_cause (live : State → Bool) (invalid cause : Cause)
    (value : Value) (state : State) (before : live state = true) :
    finiteShrinkStage (Output := Output) live invalid (fun _ _ => .error cause) value state =
      .error (some cause) := by
  simp [finiteShrinkStage, guardedGeneration, before]

/-- An admitted callback's malformed result is an error, never a usable prefix. -/
theorem finiteShrinkStage_malformed (live : State → Bool) (invalid : Cause)
    (value : Value) (state next : State) (before : live state = true) (after : live next = true) :
    finiteShrinkStage (Output := Output) live invalid (fun _ _ => .ok (none, next)) value state =
      .error (some invalid) := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Proper result order, false payloads and the resulting state are unchanged. -/
theorem finiteShrinkStage_present (live : State → Bool) (invalid : Cause)
    (values : List Output) (value : Value) (state next : State)
    (before : live state = true) (after : live next = true) :
    finiteShrinkStage live invalid (fun _ _ => .ok (some values, next)) value state = .ok (values, next) := by
  simp [finiteShrinkStage, guardedGeneration, before, after]

/-- Either source or shape refusal prevents every later preparation stage. -/
theorem finiteShrinkStage_refused (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (state : State) (cause : Option Cause)
    (next : List Output × State → Except (Option Cause) Other)
    (refused : finiteShrinkStage live invalid shrink value state = .error cause) :
    (finiteShrinkStage live invalid shrink value state >>= next) = .error cause := by
  rw [refused]; rfl

/-- Admission does not change legitimate dependency retirement: only normalized
commands may be omitted by the existing model policy, in original relative order. -/
theorem finiteSequenceInput_repair (model : TraceModel State Command Reply)
    (invalid : Cause) (commands : List Command) (state : State) :
    finiteSequenceInput invalid (some commands)
      (fun values => .ok (retire model state values)) = .ok (retire model state commands) ∧
      traceValid model state (retire model state commands) = true ∧
      (retire model state commands).Sublist commands :=
  ⟨rfl, retire_valid model commands state, retire_sublist model commands state⟩

/-- Consume an owned finite input snapshot in order. Callback state may change,
but it never supplies the next coordinate. Each result retains whole-spine and
source admission; an error publishes no partial parameter batch. Faithful host
spine copying is a premise, not a theorem about Scheme pair allocation. -/
def finiteSequenceParameters (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State)) :
    List Value → State → Except (Option Cause) (List (List Output) × State)
  | [], state => .ok ([], state)
  | value :: rest, state =>
      match finiteShrinkStage live invalid shrink value state with
      | .error cause => .error cause
      | .ok (children, next) => match finiteSequenceParameters live invalid shrink rest next with
        | .error cause => .error cause
        | .ok (tail, final) => .ok (children :: tail, final)

/-- Empty snapshots invoke no parameter stage and retain the exact state. -/
theorem finiteSequenceParameters_nil (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State)) (state : State) :
    finiteSequenceParameters live invalid shrink [] state = .ok ([], state) := rfl

/-- First-stage refusal skips every later coordinate and publishes no prefix. -/
theorem finiteSequenceParameters_head_refused (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (rest : List Value) (state : State) (cause : Option Cause)
    (refused : finiteShrinkStage live invalid shrink value state = .error cause) :
    finiteSequenceParameters live invalid shrink (value :: rest) state = .error cause := by
  simp [finiteSequenceParameters, refused]

/-- A later failure discards the already prepared head batch as well. -/
theorem finiteSequenceParameters_tail_refused (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (value : Value) (rest : List Value) (state next : State) (children : List Output)
    (cause : Option Cause)
    (head : finiteShrinkStage live invalid shrink value state = .ok (children, next))
    (tail : finiteSequenceParameters live invalid shrink rest next = .error cause) :
    finiteSequenceParameters live invalid shrink (value :: rest) state = .error cause := by
  simp [finiteSequenceParameters, head, tail]

/-- Retirement inside a callback interrupts before reading another snapshot item. -/
theorem finiteSequenceParameters_revised (live : State → Bool) (invalid : Cause)
    (value : Value) (rest : List Value) (state next : State) (children : Option (List Output))
    (before : live state = true) (after : live next = false) :
    finiteSequenceParameters live invalid (fun _ _ => .ok (children, next))
      (value :: rest) state = .error none :=
  finiteSequenceParameters_head_refused live invalid _ value rest state none
    (finiteShrinkStage_revised live invalid children value state next before after)

/-- A thrown cause remains distinct from source retirement, including false. -/
theorem finiteSequenceParameters_cause (live : State → Bool) (invalid cause : Cause)
    (value : Value) (rest : List Value) (state : State) (before : live state = true) :
    finiteSequenceParameters (Output := Output) live invalid (fun _ _ => .error cause)
      (value :: rest) state = .error (some cause) :=
  finiteSequenceParameters_head_refused live invalid _ value rest state (some cause)
    (finiteShrinkStage_cause live invalid cause value state before)

/-- A proper first result cannot turn a malformed later batch into a prefix. -/
theorem finiteSequenceParameters_malformed (live : State → Bool) (invalid : Cause)
    (value : Value) (rest : List Value) (state next : State)
    (before : live state = true) (after : live next = true) :
    finiteSequenceParameters (Output := Output) live invalid (fun _ _ => .ok (none, next))
      (value :: rest) state = .error (some invalid) :=
  finiteSequenceParameters_head_refused live invalid _ value rest state (some invalid)
    (finiteShrinkStage_malformed live invalid value state next before after)

/-- Successful preparation has exactly one batch per owned input coordinate. -/
theorem finiteSequenceParameters_length (live : State → Bool) (invalid : Cause)
    (shrink : Value → State → Except Cause (Option (List Output) × State))
    (values : List Value) (state final : State) (batches : List (List Output))
    (success : finiteSequenceParameters live invalid shrink values state = .ok (batches, final)) :
    batches.length = values.length := by
  induction values generalizing state batches with
  | nil => simp [finiteSequenceParameters] at success; obtain ⟨rfl, _⟩ := success; rfl
  | cons value rest ih =>
    cases head : finiteShrinkStage live invalid shrink value state with
    | error cause => simp [finiteSequenceParameters, head] at success
    | ok prepared =>
      obtain ⟨children, next⟩ := prepared
      cases tail : finiteSequenceParameters live invalid shrink rest next with
      | error cause => simp [finiteSequenceParameters, head, tail] at success
      | ok prepared =>
        obtain ⟨remaining, last⟩ := prepared
        simp [finiteSequenceParameters, head, tail] at success
        obtain ⟨rfl, rfl⟩ := success
        simpa using congrArg Nat.succ (ih next remaining tail)

/-- Even callbacks which replace an entire ambient list cannot change the
captured coordinate order. The callbacks here return one mapped child each;
their state changes compose normally, without rereading an ambient input. -/
theorem finiteSequenceParameters_snapshot (invalid : Cause) (project : Value → Output)
    (revise : State → State) (values : List Value) (state : State) :
    finiteSequenceParameters (fun _ => true) invalid
      (fun value state => .ok (some [project value], revise state)) values state =
      .ok (values.map (fun value => [project value]), values.foldl (fun state _ => revise state) state) := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
    simp [finiteSequenceParameters, finiteShrinkStage, guardedGeneration, ih]

/-- Sum alternatives retain labels separately from shared payload node identities.
Only branches with a finite witness inside the residual allowance are selectable. -/
def eligibleTaggedBranches (branches : List (Tag × Nat)) (cost : Nat → Option Nat)
    (available : Nat) : List (Tag × Nat) :=
  branches.filter (fun branch => (cost branch.2).any (fun needed => decide (needed ≤ available)))

/-- Filtering preserves declaration order, including distinct labels sharing a node. -/
theorem eligibleTaggedBranches_order (branches : List (Tag × Nat)) (cost : Nat → Option Nat)
    (available : Nat) : (eligibleTaggedBranches branches cost available).Sublist branches :=
  List.filter_sublist

/-- Every selectable alternative has an original label/node pair and affordable cost. -/
theorem eligibleTaggedBranches_sound (branches : List (Tag × Nat)) (cost : Nat → Option Nat)
    (available node : Nat) (tag : Tag)
    (chosen : (tag, node) ∈ eligibleTaggedBranches branches cost available) :
    (tag, node) ∈ branches ∧ ∃ needed, cost node = some needed ∧ needed ≤ available := by
  obtain ⟨member, fits⟩ := List.mem_filter.mp chosen
  refine ⟨member, ?_⟩
  cases found : cost node with
  | none => simp [found] at fits
  | some needed => exact ⟨needed, rfl, by simpa [found] using fits⟩

/-- Empty or entirely uninhabited declarations provide no branch to sample. -/
theorem eligibleTaggedBranches_empty (cost : Nat → Option Nat) (available : Nat) :
    eligibleTaggedBranches ([] : List (Tag × Nat)) cost available = [] := rfl

/-- Reserving the Sum root leaves enough quota for every selected child. -/
theorem taggedBranch_total_budget (remaining needed : Nat) (positive : 0 < remaining)
    (fits : needed ≤ remaining - 1) : 1 + needed ≤ remaining := by omega

/-- Payload shrinking retains its captured label; no redispatch or redraw occurs. -/
def taggedCandidates (tag : Tag) (payloads : List Value) : List (Tag × Value) :=
  payloads.map (fun value => (tag, value))

/-- Both the label and payload provenance survive each proposed shrink. -/
theorem taggedCandidates_member (tag label : Tag) (payloads : List Value) (value : Value) :
    (label, value) ∈ taggedCandidates tag payloads ↔ label = tag ∧ value ∈ payloads := by
  simp only [taggedCandidates, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨candidate, member, same, rfl⟩
    exact ⟨same.symm, member⟩
  · rintro ⟨rfl, member⟩
    exact ⟨value, member, rfl, rfl⟩

/-- Adding the fixed carrier-root cost cannot manufacture or hide strict descent. -/
theorem taggedCandidates_descent (measure : Value → Nat) (original smaller : Value) :
    1 + measure smaller < 1 + measure original ↔ measure smaller < measure original := by omega

/-- Read the payload only after its label identifies a captured branch. The host
interpretation supplies truthful getters and bounded, source-current inspection. -/
def inspectTagged [DecidableEq Tag] (branches : List (Tag × Nat)) (tag : Tag)
    (read : Unit → Except Cause Value) (inspect : Nat → Value → Except Cause (Option Output)) :
    Except Cause (Option (Tag × Output)) :=
  match lookupFunction branches tag with
  | none => .ok none
  | some node => do
    let value ← read ()
    let child ← inspect node value
    pure (child.map (fun payload => (tag, payload)))

/-- Unknown labels cannot invoke a payload getter or branch inspector. -/
theorem inspectTagged_unknown [DecidableEq Tag] (branches : List (Tag × Nat)) (tag : Tag)
    (read : Unit → Except Cause Value) (inspect : Nat → Value → Except Cause (Option Output))
    (missing : lookupFunction branches tag = none) :
    inspectTagged branches tag read inspect = .ok none := by simp [inspectTagged, missing]

/-- Getter failures preserve their exact cause and suppress payload inspection. -/
theorem inspectTagged_read_error [DecidableEq Tag] (branches : List (Tag × Nat)) (tag : Tag)
    (node : Nat) (cause : Cause) (inspect : Nat → Value → Except Cause (Option Output))
    (selected : lookupFunction branches tag = some node) :
    inspectTagged branches tag (fun _ => .error cause) inspect = .error cause := by
  simp only [inspectTagged, selected]
  rfl

/-- Successful inspection retains the selected label even with shared child nodes. -/
theorem inspectTagged_success [DecidableEq Tag] (branches : List (Tag × Nat)) (tag : Tag)
    (node : Nat) (value : Value) (payload : Output)
    (inspect : Nat → Value → Except Cause (Option Output))
    (selected : lookupFunction branches tag = some node)
    (accepted : inspect node value = .ok (some payload)) :
    inspectTagged branches tag (fun _ => .ok value) inspect = .ok (some (tag, payload)) := by
  simp only [inspectTagged, selected]
  change (inspect node value).map (fun child => child.map (fun item => (tag, item))) = _
  rw [accepted]
  rfl

/-- Text carriers map the same spelling neighborhood through one representation. -/
def spellingCandidates (pack : Spelling → Carrier) (shrink : Spelling → List Spelling)
    (unpack : Carrier → Spelling) (value : Carrier) : List Carrier :=
  (shrink (unpack value)).map pack

/-- A faithful standard codec recovers every proposed spelling in the same order. -/
theorem spellingCandidates_decode (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (roundtrip : ∀ text, unpack (pack text) = text)
    (shrink : Spelling → List Spelling) (value : Carrier) :
    (spellingCandidates pack shrink unpack value).map unpack = shrink (unpack value) := by
  simp [spellingCandidates, List.map_map, Function.comp_def, roundtrip]

/-- Mapping does not resample, drop or duplicate proposals. -/
theorem spellingCandidates_length (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (shrink : Spelling → List Spelling) (value : Carrier) :
    (spellingCandidates pack shrink unpack value).length = (shrink (unpack value)).length := by
  simp [spellingCandidates]

/-- Every materialized proposal has an original spelling, not another carrier. -/
theorem spellingCandidates_origin (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (shrink : Spelling → List Spelling) (value candidate : Carrier)
    (member : candidate ∈ spellingCandidates pack shrink unpack value) :
    ∃ text ∈ shrink (unpack value), pack text = candidate := List.mem_map.mp member

/-- Strict content ranking survives representation conversion without new checks. -/
theorem spellingCandidates_descent (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (roundtrip : ∀ text, unpack (pack text) = text)
    (weight : Spelling → Nat) (shrink : Spelling → List Spelling)
    (strict : ∀ text child, child ∈ shrink text → weight child < weight text)
    (value candidate : Carrier)
    (member : candidate ∈ spellingCandidates pack shrink unpack value) :
    weight (unpack candidate) < weight (unpack value) := by
  obtain ⟨text, child, rfl⟩ := spellingCandidates_origin pack unpack shrink value candidate member
  rw [roundtrip]
  exact strict _ _ child

/-- Declared alphabets/length domains survive when the codec and source shrinker do. -/
theorem spellingCandidates_domain (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (roundtrip : ∀ text, unpack (pack text) = text)
    (allowed : Spelling → Prop) (shrink : Spelling → List Spelling)
    (preserves : ∀ text child, allowed text → child ∈ shrink text → allowed child)
    (value candidate : Carrier) (valid : allowed (unpack value))
    (member : candidate ∈ spellingCandidates pack shrink unpack value) : allowed (unpack candidate) := by
  obtain ⟨text, child, rfl⟩ := spellingCandidates_origin pack unpack shrink value candidate member
  rw [roundtrip]
  exact preserves _ _ valid child

/-- The empty spelling stays terminal when its underlying neighborhood is empty. -/
theorem spellingCandidates_terminal (pack : Spelling → Carrier) (unpack : Carrier → Spelling)
    (shrink : Spelling → List Spelling) (value : Carrier)
    (terminal : shrink (unpack value) = []) : spellingCandidates pack shrink unpack value = [] := by
  simp [spellingCandidates, terminal]

end LeanPoo.Functional.PropertyTesting
