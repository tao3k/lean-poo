import LeanPoo.Functional.PropertySequences

/-! Portable authority and bounded-copy preparation. Boolean source judgments
share their owner with typed preparation; child costs include roots and compact
payloads. Faithful source normalization, pure observers, cost profiles and host
vector/port behavior are premises, not verified here. -/
namespace LeanPoo.Functional.PropertyTesting

/-- The core source-observer contract admits only actual Booleans. None denotes
any non-Boolean host datum, not false authority or absence of an optional hook. -/
def sourceReply (malformed : Cause) : Option Bool → Except Cause Bool
  | none => .error malformed
  | some value => .ok value

/-- Codec authority precedes application authority. Observers are pure at each
state: none is a malformed host reply, false is ordinary source retirement. -/
def replayAuthority (malformed staleCodec staleContext : Cause)
    (codec context : State → Except Cause (Option Bool)) (state : State) : Except Cause Unit := do
  let first ← codec state
  let live ← sourceReply malformed first
  if !live then .error staleCodec else do
    let second ← context state
    let live ← sourceReply malformed second
    if live then .ok () else .error staleContext

/-- Both normal boundaries use the same authority judgment. Callback exceptions
bypass the trailing check unchanged; a rejected normal result is not published.
Effects already performed by the action are not rolled back. -/
def checkedReplayAction (malformed staleCodec staleContext : Cause)
    (codec context : State → Except Cause (Option Bool))
    (action : State → Except Cause (Value × State)) (state : State) : Except Cause (Value × State) :=
  match replayAuthority malformed staleCodec staleContext codec context state with
  | .error cause => .error cause
  | .ok () => match action state with
    | .error cause => .error cause
    | .ok result => match replayAuthority malformed staleCodec staleContext codec context result.2 with
      | .error cause => .error cause
      | .ok () => .ok result

/-- Malformed codec replies suppress application observation, not just delivery. -/
theorem replayAuthority_malformed_codec (bad staleCodec staleContext : Cause)
    (context : State → Except Cause (Option Bool)) (state : State) :
    replayAuthority bad staleCodec staleContext (fun _ => .ok none) context state = .error bad := rfl

/-- A false codec still has the original codec-first stale diagnostic. -/
theorem replayAuthority_false_codec (bad staleCodec staleContext : Cause)
    (context : State → Except Cause (Option Bool)) (state : State) :
    replayAuthority bad staleCodec staleContext (fun _ => .ok (some false)) context state = .error staleCodec := rfl

/-- Observer exceptions, even a cause representing Scheme false, remain exact. -/
theorem replayAuthority_codec_cause (bad staleCodec staleContext cause : Cause)
    (context : State → Except Cause (Option Bool)) (state : State) :
    replayAuthority bad staleCodec staleContext (fun _ => .error cause) context state = .error cause := rfl

/-- A live codec cannot authorize a malformed application reply. -/
theorem replayAuthority_malformed_context (bad staleCodec staleContext : Cause) (state : State) :
    replayAuthority bad staleCodec staleContext (fun _ => .ok (some true)) (fun _ => .ok none) state = .error bad := rfl

/-- False context authority retains its distinct stale-context diagnostic. -/
theorem replayAuthority_false_context (bad staleCodec staleContext : Cause) (state : State) :
    replayAuthority bad staleCodec staleContext (fun _ => .ok (some true))
      (fun _ => .ok (some false)) state = .error staleContext := rfl

/-- Any refused preflight skips the action, regardless of its latent exception. -/
theorem checkedReplayAction_refused (bad staleCodec staleContext cause : Cause)
    (codec context : State → Except Cause (Option Bool))
    (action : State → Except Cause (Value × State)) (state : State)
    (refused : replayAuthority bad staleCodec staleContext codec context state = .error cause) :
    checkedReplayAction bad staleCodec staleContext codec context action state = .error cause := by
  simp [checkedReplayAction, refused]

/-- An admitted callback's own exception bypasses any later observer failure. -/
theorem checkedReplayAction_cause (bad staleCodec staleContext cause : Cause)
    (codec context : State → Except Cause (Option Bool)) (state : State)
    (admitted : replayAuthority bad staleCodec staleContext codec context state = .ok ()) :
    checkedReplayAction bad staleCodec staleContext codec context
      (fun _ => (.error cause : Except Cause (Value × State))) state = .error cause := by
  simp [checkedReplayAction, admitted]

/-- A changed normal return is refused at the same trailing authority boundary. -/
theorem checkedReplayAction_trailing (bad staleCodec staleContext cause : Cause)
    (codec context : State → Except Cause (Option Bool)) (state next : State) (value : Value)
    (before : replayAuthority bad staleCodec staleContext codec context state = .ok ())
    (after : replayAuthority bad staleCodec staleContext codec context next = .error cause) :
    checkedReplayAction bad staleCodec staleContext codec context (fun _ => .ok (value, next)) state = .error cause := by
  simp [checkedReplayAction, before, after]

/-- Stable authority preserves the callback value and final state without rewriting. -/
theorem checkedReplayAction_stable (bad staleCodec staleContext : Cause)
    (codec context : State → Except Cause (Option Bool)) (state next : State) (value : Value)
    (before : replayAuthority bad staleCodec staleContext codec context state = .ok ())
    (after : replayAuthority bad staleCodec staleContext codec context next = .ok ()) :
    checkedReplayAction bad staleCodec staleContext codec context (fun _ => .ok (value, next)) state = .ok (value, next) := by
  simp [checkedReplayAction, before, after]

/-- A vector needs room for every child root and, unless empty, a child depth. -/
def replayVectorReady (remaining depth width : Nat) : Bool :=
  decide (width ≤ remaining ∧ (width = 0 ∨ 0 < depth))

/-- Admission precedes destination allocation and child inspection. The action
models those host operations; rejected preparation does not evaluate it. -/
def admitReplayVector (remaining depth width : Nat) (allocate : Nat → Except Cause Value) :
    Except (Option Cause) Value :=
  if replayVectorReady remaining depth width then (allocate width).mapError some else .error none

/-- A single remaining allowance is threaded through successive child copies. -/
def replayCopyCosts : List Nat → Nat → Option Nat
  | [], remaining => some remaining
  | cost :: rest, remaining =>
    if cost ≤ remaining then replayCopyCosts rest (remaining - cost) else none

/-- Successful copying accounts for every compact/nested payload unit exactly. -/
theorem replayCopyCosts_accounting (costs : List Nat) (remaining after : Nat)
    (success : replayCopyCosts costs remaining = some after) :
    after + costs.sum = remaining := by
  induction costs generalizing remaining with
  | nil => simpa [replayCopyCosts] using success.symm
  | cons cost rest ih =>
    by_cases fits : cost ≤ remaining
    · simp [replayCopyCosts, fits] at success
      have charged := ih (remaining - cost) success
      simp only [List.sum_cons]
      omega
    · simp [replayCopyCosts, fits] at success

/-- Every child has at least its own root: width is a necessary lower bound. -/
theorem replayCopyCosts_minimum (costs : List Nat) :
    (∀ cost ∈ costs, 0 < cost) → costs.length ≤ costs.sum := by
  induction costs with
  | nil => simp
  | cons cost rest ih =>
    intro positive
    have head := positive cost (by simp)
    have tail := ih (fun value member => positive value (by simp [member]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Width preflight cannot exclude a feasible positive-cost child profile. -/
theorem replayVectorReady_necessary (costs : List Nat) (remaining after depth : Nat)
    (positive : ∀ cost ∈ costs, 0 < cost)
    (success : replayCopyCosts costs remaining = some after) :
    replayVectorReady remaining (depth + 1) costs.length = true := by
  have charged := replayCopyCosts_accounting costs remaining after success
  have minimum := replayCopyCosts_minimum costs positive
  have width : costs.length ≤ remaining := by omega
  simp [replayVectorReady, width]

/-- Oversized vectors refuse before allocating or visiting even their first child. -/
theorem admitReplayVector_wide (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (oversized : remaining < width) :
    admitReplayVector remaining depth width allocate = .error none := by
  simp [admitReplayVector, replayVectorReady, Nat.not_le.mpr oversized]

/-- A nonempty vector cannot allocate a destination at exhausted child depth. -/
theorem admitReplayVector_depth (remaining width : Nat)
    (allocate : Nat → Except Cause Value) (nonempty : width ≠ 0) :
    admitReplayVector remaining 0 width allocate = .error none := by
  simp [admitReplayVector, replayVectorReady, nonempty]

/-- Empty vectors remain data at depth zero and require no child-node credits. -/
theorem admitReplayVector_empty (remaining : Nat) (allocate : Nat → Except Cause Value) :
    admitReplayVector remaining 0 0 allocate = (allocate 0).mapError some := by
  simp [admitReplayVector, replayVectorReady]

/-- Feasible preparation preserves the exact action, including its exception. -/
theorem admitReplayVector_preserves (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (ready : replayVectorReady remaining depth width = true) :
    admitReplayVector remaining depth width allocate = (allocate width).mapError some := by
  simp [admitReplayVector, ready]

/-- Any admitted vector destination has width bounded by the remaining credits. -/
theorem admitReplayVector_width (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (value : Value)
    (success : admitReplayVector remaining depth width allocate = .ok value) :
    width ≤ remaining := by
  by_cases ready : replayVectorReady remaining depth width = true
  · have bounds : width ≤ remaining ∧ (width = 0 ∨ 0 < depth) := by
      simpa [replayVectorReady] using ready
    exact bounds.1
  · simp [admitReplayVector, ready] at success

/-- Pure request admission precedes source observers, callbacks and host I/O. -/
def admitReplayRequest (valid : Bool) (invalid : Cause)
    (action : State → Except (Option Cause) Value) (state : State) :
    Except (Option Cause) Value :=
  if valid then action state else .error (some invalid)

/-- Reader EOF and physical EOF are distinct observations. Each host action has
its own existing source boundary; normal source retirement precedes classification.
Faithful port observations and terminating host actions are explicit premises. -/
def replayInputEnd (live : State → Bool) (invalid : Cause)
    (read peek : State → Except Cause (Bool × State)) (state : State) :
    Except (Option Cause) (Unit × State) :=
  match guardedGeneration live read state with
  | .error cause => .error cause
  | .ok (false, _) => .error (some invalid)
  | .ok (true, next) =>
    match guardedGeneration live peek next with
    | .error cause => .error cause
    | .ok (false, _) => .error (some invalid)
    | .ok (true, after) => .ok ((), after)

/-- Invalid static configuration cannot enter the supplied action. -/
theorem admitReplayRequest_invalid (invalid : Cause)
    (action : State → Except (Option Cause) Value) (state : State) :
    admitReplayRequest false invalid action state = .error (some invalid) := rfl

/-- Valid static configuration preserves the exact action result. -/
theorem admitReplayRequest_valid (invalid : Cause)
    (action : State → Except (Option Cause) Value) (state : State) :
    admitReplayRequest true invalid action state = action state := rfl

/-- Stale input preparation skips both host observations. -/
theorem replayInputEnd_stale (live : State → Bool) (invalid : Cause)
    (read peek : State → Except Cause (Bool × State)) (state : State)
    (stale : live state = false) :
    replayInputEnd live invalid read peek state = .error none := by
  simp [replayInputEnd, guardedGeneration, stale]

/-- A real trailing datum refuses before the physical probe. -/
theorem replayInputEnd_datum (live : State → Bool) (invalid : Cause)
    (peek : State → Except Cause (Bool × State)) (state next : State)
    (before : live state = true) (after : live next = true) :
    replayInputEnd live invalid (fun _ => .ok (false, next)) peek state =
      .error (some invalid) := by
  simp [replayInputEnd, guardedGeneration, before, after]

/-- An explicit reader EOF cannot hide remaining physical input. -/
theorem replayInputEnd_pending (live : State → Bool) (invalid : Cause)
    (state next after : State) (a : live state = true) (b : live next = true)
    (c : live after = true) :
    replayInputEnd live invalid (fun _ => .ok (true, next))
      (fun _ => .ok (false, after)) state = .error (some invalid) := by
  simp [replayInputEnd, guardedGeneration, a, b, c]

/-- Two successful EOF observations retain the final host state. -/
theorem replayInputEnd_complete (live : State → Bool) (invalid : Cause)
    (state next after : State) (a : live state = true) (b : live next = true)
    (c : live after = true) :
    replayInputEnd live invalid (fun _ => .ok (true, next))
      (fun _ => .ok (true, after)) state = .ok ((), after) := by
  simp [replayInputEnd, guardedGeneration, a, b, c]

/-- Reader exceptions retain their original cause, including a false cause. -/
theorem replayInputEnd_read_cause (live : State → Bool) (invalid cause : Cause)
    (peek : State → Except Cause (Bool × State)) (state : State)
    (before : live state = true) :
    replayInputEnd live invalid (fun _ => .error cause) peek state = .error (some cause) := by
  simp [replayInputEnd, guardedGeneration, before]

/-- Reader source retirement skips the physical probe even after normal EOF. -/
theorem replayInputEnd_read_revised (live : State → Bool) (invalid : Cause)
    (peek : State → Except Cause (Bool × State)) (state next : State)
    (before : live state = true) (after : live next = false) :
    replayInputEnd live invalid (fun _ => .ok (true, next)) peek state = .error none := by
  simp [replayInputEnd, guardedGeneration, before, after]

/-- Physical probe exceptions remain exact after successful reader admission. -/
theorem replayInputEnd_peek_cause (live : State → Bool) (invalid cause : Cause)
    (state next : State) (before : live state = true) (after : live next = true) :
    replayInputEnd live invalid (fun _ => .ok (true, next))
      (fun _ => .error cause) state = .error (some cause) := by
  simp [replayInputEnd, guardedGeneration, before, after]

/-- Probe source retirement precedes interpreting its returned physical flag. -/
theorem replayInputEnd_peek_revised (live : State → Bool) (invalid : Cause)
    (state next after : State) (flag : Bool) (a : live state = true)
    (b : live next = true) (c : live after = false) :
    replayInputEnd live invalid (fun _ => .ok (true, next))
      (fun _ => .ok (flag, after)) state = .error none := by
  simp [replayInputEnd, guardedGeneration, a, b, c]

/-- Refused framing cannot enter decoding or any dependent property action. -/
theorem replayInputEnd_refused (live : State → Bool) (invalid : Cause)
    (read peek : State → Except Cause (Bool × State)) (state : State)
    (decode : Unit × State → Except (Option Cause) Value) (cause : Option Cause)
    (refused : replayInputEnd live invalid read peek state = .error cause) :
    (replayInputEnd live invalid read peek state >>= decode) = .error cause := by
  rw [refused]; rfl

/-- Tokens are the symbols/keywords encountered by a faithful finite data walk.
Only stable interned identities enter the existing request/action boundary;
the host copier never repairs a fresh identity by interning its spelling. -/
def admitReplayTokens (interned : Token → Bool) (tokens : List Token) (invalid : Cause)
    (action : State → Except (Option Cause) Value) (state : State) :
    Except (Option Cause) Value :=
  admitReplayRequest (tokens.all interned) invalid action state

/-- Every encountered token is stable after successful token admission. -/
theorem replayTokens_sound (interned : Token → Bool) (tokens : List Token)
    (ready : tokens.all interned = true) (token : Token) (member : token ∈ tokens) :
    interned token = true := by
  exact List.all_eq_true.mp ready token member

/-- Nesting cannot hide a fresh token: the complete encountered directory refuses. -/
theorem replayTokens_uninterned (interned : Token → Bool) (tokens : List Token)
    (token : Token) (member : token ∈ tokens) (fresh : interned token = false) :
    tokens.all interned = false := by
  cases ready : tokens.all interned with
  | false => rfl
  | true => have accepted := replayTokens_sound interned tokens ready token member
            simp [fresh] at accepted

/-- Identity and payload token directories share the same conjunctive rule. -/
theorem replayTokens_append (interned : Token → Bool) (identity payload : List Token) :
    (identity ++ payload).all interned = (identity.all interned && payload.all interned) := by
  simp

/-- Refused token data cannot enter allocation, output delivery or decoding. -/
theorem admitReplayTokens_refused (interned : Token → Bool) (tokens : List Token)
    (invalid : Cause) (action : State → Except (Option Cause) Value) (state : State)
    (refused : tokens.all interned = false) :
    admitReplayTokens interned tokens invalid action state = .error (some invalid) := by
  simp [admitReplayTokens, refused, admitReplayRequest]

/-- Stable tokens preserve the exact existing action, without normalizing values. -/
theorem admitReplayTokens_preserves (interned : Token → Bool) (tokens : List Token)
    (invalid : Cause) (action : State → Except (Option Cause) Value) (state : State)
    (ready : tokens.all interned = true) :
    admitReplayTokens interned tokens invalid action state = action state := by
  simp [admitReplayTokens, ready, admitReplayRequest]

/-- Empty token directories preserve ordinary data, including false witnesses. -/
theorem admitReplayTokens_empty (interned : Token → Bool) (invalid : Cause)
    (action : State → Except (Option Cause) Value) (state : State) :
    admitReplayTokens interned [] invalid action state = action state := rfl

/-- Valid data retain stale refusal and exact callback errors as distinct results. -/
theorem admitReplayTokens_cause (interned : Token → Bool) (tokens : List Token)
    (invalid : Cause) (cause : Option Cause) (state : State)
    (ready : tokens.all interned = true) :
    admitReplayTokens interned tokens invalid
      (fun _ => (.error cause : Except (Option Cause) Value)) state = .error cause := by
  exact admitReplayTokens_preserves interned tokens invalid _ state ready

/-- Standard reader/writer identity is a premise for interned host tokens. Under
that premise a portable directory retains every identity and its original order. -/
theorem replayTokens_roundtrip (interned : Token → Bool) (roundtrip : Token → Token)
    (stable : ∀ token, interned token = true → roundtrip token = token)
    (tokens : List Token) (ready : tokens.all interned = true) :
    tokens.map roundtrip = tokens := by
  have same : tokens.map roundtrip = tokens.map id := by
    apply List.map_congr_left
    intro token member
    exact stable token (replayTokens_sound interned tokens ready token member)
  simpa using same

/-- A failing identity-sensitive property cannot become passing solely through
standard serialization of admitted tokens. Other codec laws remain explicit. -/
theorem replayTokens_failure (interned : Token → Bool) (roundtrip : Token → Token)
    (stable : ∀ token, interned token = true → roundtrip token = token)
    (tokens : List Token) (ready : tokens.all interned = true)
    (property : List Token → Bool) (failed : property tokens = false) :
    property (tokens.map roundtrip) = false := by
  rw [replayTokens_roundtrip interned roundtrip stable tokens ready]
  exact failed

end LeanPoo.Functional.PropertyTesting
