import LeanPoo.Functional.TableRepresentation
import LeanPoo.Prototype.LinearState

/-! Generated collection styles over one persistent backend. The model covers
atomic staged updates and dynamic ownership, not static linear types or rollback
of arbitrary callback effects. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Pure values, stable mutable identities, and consume-old/return-new references. -/
inductive TableStyle where
  | pure | mutable | linear
  deriving DecidableEq, Repr

/-- Ownership refusal is separate from an unchanged original backend cause. -/
inductive StyleFailure (E : Type) where
  | consumed | stale | callback (cause : E)
  deriving DecidableEq, Repr

/-- One atomic table transformation; a failure exposes no intermediate writes. -/
def styleStep (style : TableStyle) (state : Option A) (update : A → Except E A) :
    Option A × Except (StyleFailure E) A :=
  match state with
  | none => (none, .error .consumed)
  | some before =>
    match update before with
    | .error cause => (state, .error (.callback cause))
    | .ok after =>
      (match style with
       | .pure => state
       | .mutable => some after
       | .linear => none, .ok after)

/-- Pure snapshots are duplicable; converting any owned reference retires aliases.
The target receives the exact admitted payload in a separately prepared successor. -/
def styleConvert (source target : TableStyle) (state : Option A) :
    Option A × Except (StyleFailure E) (TableStyle × A) :=
  match state with
  | none => (none, .error .consumed)
  | some value => (if source = .pure then state else none, .ok (target, value))

/-- The successful result is independent of style, including exact failure causes. -/
theorem styleStep_result (left right : TableStyle) (state : Option A) (update : A → Except E A) :
    (styleStep left state update).2 = (styleStep right state update).2 := by
  cases state with
  | none => rfl
  | some before => cases h : update before <;> simp [styleStep, h]

/-- Callback refusal preserves the original reference and cause in every style. -/
theorem styleStep_failure (style : TableStyle) (before : A) (update : A → Except E A)
    (cause : E) (h : update before = .error cause) :
    styleStep style (some before) update = (some before, .error (.callback cause)) := by
  simp [styleStep, h]

/-- No callback is evaluated after ownership has been consumed. -/
theorem styleStep_consumed (style : TableStyle) (update : A → Except E A) :
    styleStep style none update = (none, .error .consumed) := rfl

/-- Pure update returns the new value while retaining the entire prior snapshot. -/
theorem styleStep_pure (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .pure (some before) update = (some before, .ok after) := by simp [styleStep, h]

/-- Mutable update changes the payload of the one retained identity. -/
theorem styleStep_mutable (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .mutable (some before) update = (some after, .ok after) := by simp [styleStep, h]

/-- Linear success retires every old alias and returns the successor payload. -/
theorem styleStep_linear (before after : A) (update : A → Except E A)
    (h : update before = .ok after) :
    styleStep .linear (some before) update = (none, .ok after) := by simp [styleStep, h]

/-- All nine conversions preserve the same observed payload and exact target style. -/
theorem styleConvert_observation (source target : TableStyle) (value : A) :
    (styleConvert (E := E) source target (some value)).2 = .ok (target, value) := rfl

/-- Owned conversion consumes the source even when the target has the same style. -/
theorem styleConvert_owned (source target : TableStyle) (value : A) (owned : source ≠ .pure) :
    (styleConvert (E := E) source target (some value)).1 = none := by simp [styleConvert, owned]

/-- Pure conversion does not retire the original duplicable snapshot. -/
theorem styleConvert_pure (target : TableStyle) (value : A) :
    (styleConvert (E := E) .pure target (some value)).1 = some value := by simp [styleConvert]

/-- Conversion cannot revive a consumed owner. -/
theorem styleConvert_consumed (source target : TableStyle) :
    styleConvert (A := A) (E := E) source target none = (none, .error .consumed) := rfl

/-- The atomic linear specialization reuses the existing partial-state reference
semantics by retaining before on error. It does not change that lower-level API. -/
theorem styleStep_linear_existing (before : A) (update : A → Except String A) :
    styleStep .linear (some before) update =
      Prod.map id (fun result => result.mapError StyleFailure.callback)
      (LeanPoo.Prototype.LinearState.stepValue (some before) (fun value =>
        match update value with
        | .error cause => (value, .error cause)
        | .ok after => (after, .ok ()))) := by
  cases h : update before <;> simp [styleStep, LeanPoo.Prototype.LinearState.stepValue, Except.mapError, h]

/-- A private immutable generation distinguishes ABA changes even at equal values. -/
structure TableGeneration (A : Type) where
  version : Nat
  value : Option A
  deriving DecidableEq, Repr

/-- Installation checks a captured generation before applying any staged result. -/
def installStyle (style : TableStyle) (current : TableGeneration A) (expected : Nat)
    (after : A) : TableGeneration A × Except (StyleFailure E) A :=
  if current.version ≠ expected ∨ current.value.isNone then
    (current, .error .stale)
  else
    (⟨current.version + 1, if style = .linear then none else some after⟩, .ok after)

/-- A losing callback cannot overwrite or resurrect a newer generation. -/
theorem installStyle_stale (style : TableStyle) (current : TableGeneration A) (expected : Nat)
    (after : A) (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected after = (current, .error .stale) := by
  simp [installStyle, stale]

/-- A retired head refuses installation even if its version matches. -/
theorem installStyle_retired (style : TableStyle) (version : Nat) (after : A) :
    installStyle (E := E) style ⟨version, none⟩ version after =
      (⟨version, none⟩, .error .stale) := by simp [installStyle]

/-- Returning to an equal table value still invalidates an earlier staged update. -/
theorem installStyle_aba (style : TableStyle) (version : Nat) (before after : A) :
    installStyle (E := E) style ⟨version + 2, some before⟩ version after =
      (⟨version + 2, some before⟩, .error .stale) := by simp [installStyle]

/-- The first installed owned successor invalidates every request with the same
captured generation, regardless of its payload or chosen reference style. -/
theorem installStyle_single_winner (style other : TableStyle) (version : Nat)
    (before first second : A) :
    let winner := (installStyle (E := E) style ⟨version, some before⟩ version first).1
    installStyle (E := E) other winner version second = (winner, .error .stale) := by
  dsimp
  apply installStyle_stale
  simp [installStyle]

/-- Exact whole-batch carrier execution supplies the same success to every style. -/
theorem styleStep_table_success [DecidableEq K] [DecidableEq V]
    (ops : TableCarrier K V A) (style : TableStyle) (edits : List (Change K V))
    (before after : A) (h : ops.apply edits before = .ok after) :
    (styleStep style (some before) (ops.apply edits)).2 = .ok after := by simp [styleStep, h]

/-- A late delta conflict keeps the whole old snapshot, not a partially edited root. -/
theorem styleStep_table_conflict [DecidableEq K] [DecidableEq V]
    (ops : TableCarrier K V A) (style : TableStyle) (edits : List (Change K V))
    (before : A) (key : K) (h : ops.apply edits before = .error key) :
    styleStep style (some before) (ops.apply edits) = (some before, .error (.callback key)) :=
  styleStep_failure style before (ops.apply edits) key h

/-- Posh and classy are receiver-bound presentations of pure and mutable style.
Their runtime class dispatch is supplied by Gerbil, not a second table backend. -/
inductive ReceiverStyle where
  | posh | classy
  deriving DecidableEq, Repr

/-- Forget only the presentation, retaining the existing ownership policy. -/
def ReceiverStyle.base : ReceiverStyle → TableStyle
  | .posh => .pure
  | .classy => .mutable

/-- Prepare a complete result representation before changing ownership. This
models receiver allocation/admission failure; it never rolls back callback IO. -/
def prepareStyleStep (style : TableStyle) (state : Option A)
    (update : A → Except E A) (prepare : A → Except E R) :
    Option A × Except (StyleFailure E) R :=
  match state with
  | none => (none, .error .consumed)
  | some before =>
    match update before with
    | .error cause => (state, .error (.callback cause))
    | .ok after =>
      match prepare after with
      | .error cause => (state, .error (.callback cause))
      | .ok result =>
        ((styleStep (E := E) style state (fun _ => .ok after)).1, .ok result)

/-- A failed presentation cannot consume a linear owner or mutate a classy head. -/
theorem prepareStyleStep_refused (style : TableStyle) (before after : A)
    (update : A → Except E A) (prepare : A → Except E R) (cause : E)
    (updated : update before = .ok after) (refused : prepare after = .error cause) :
    prepareStyleStep style (some before) update prepare =
      (some before, .error (.callback cause)) := by
  simp [prepareStyleStep, updated, refused]

/-- Successful preparation changes no ownership rule of the existing engine. -/
theorem prepareStyleStep_commutes (style : TableStyle) (before after : A)
    (update : A → Except E A) (prepare : A → Except E R) (result : R)
    (updated : update before = .ok after) (prepared : prepare after = .ok result) :
    prepareStyleStep style (some before) update prepare =
      ((styleStep style (some before) update).1, .ok result) := by
  simp [prepareStyleStep, updated, prepared, styleStep]

/-- An authentic receiver retains its originating protocol family and host identity.
A retired mutable receiver has no payload; payload snapshots remain shareable. -/
structure TableReceiver (A : Type) where
  family : Nat
  style : ReceiverStyle
  identity : Nat
  value : Option A
  deriving DecidableEq, Repr

/-- Receiver-bound dispatch reuses staged style execution. A posh successor uses
an externally fresh host identity; classy returns the same host identity. -/
def receiverStep (input : TableReceiver A) (fresh : Nat) (update : A → Except E A) :
    TableReceiver A × Except (StyleFailure E) (TableReceiver A) :=
  let staged := prepareStyleStep input.style.base input.value update (fun after =>
    .ok { input with identity := if input.style = .posh then fresh else input.identity,
                     value := some after })
  ({ input with value := staged.1 }, staged.2)

/-- Exact callback refusal retains family, identity, ownership and the cause. -/
theorem receiverStep_failure (input : TableReceiver A) (fresh : Nat)
    (before : A) (update : A → Except E A) (cause : E)
    (live : input.value = some before) (refused : update before = .error cause) :
    receiverStep input fresh update = (input, .error (.callback cause)) := by
  cases input
  simp_all [receiverStep, prepareStyleStep]

/-- Posh keeps the entire old receiver while returning a new admitted snapshot. -/
theorem receiverStep_posh (family identity fresh : Nat) (before after : A)
    (update : A → Except E A) (updated : update before = .ok after) :
    receiverStep ⟨family, .posh, identity, some before⟩ fresh update =
      (⟨family, .posh, identity, some before⟩,
       .ok ⟨family, .posh, fresh, some after⟩) := by
  simp [receiverStep, prepareStyleStep, ReceiverStyle.base, styleStep, updated]

/-- Classy preserves its receiver identity and family while replacing one head. -/
theorem receiverStep_classy (family identity fresh : Nat) (before after : A)
    (update : A → Except E A) (updated : update before = .ok after) :
    receiverStep ⟨family, .classy, identity, some before⟩ fresh update =
      (⟨family, .classy, identity, some after⟩,
       .ok ⟨family, .classy, identity, some after⟩) := by
  simp [receiverStep, prepareStyleStep, ReceiverStyle.base, styleStep, updated]

/-- A retired classy alias refuses before evaluating a new update. -/
theorem receiverStep_retired (family identity fresh : Nat) (update : A → Except E A) :
    receiverStep ⟨family, .classy, identity, none⟩ fresh update =
      (⟨family, .classy, identity, none⟩, .error .consumed) := rfl

/-- Forgetting receiver presentation commutes with the existing style transition. -/
theorem receiverStep_observation (input : TableReceiver A) (fresh : Nat)
    (update : A → Except E A) :
    ((receiverStep input fresh update).1.value,
     (receiverStep input fresh update).2.map TableReceiver.value) =
    ((styleStep input.style.base input.value update).1,
     (styleStep input.style.base input.value update).2.map some) := by
  cases input with
  | mk family style identity value =>
    cases value with
    | none => rfl
    | some before =>
      cases h : update before <;>
        simp [receiverStep, prepareStyleStep, styleStep, h, Except.map]

/-- Every receiver uses the original generation comparison for competing installs. -/
theorem receiver_install_stale (style : ReceiverStyle) (current : TableGeneration A)
    (expected : Nat) (after : A) (stale : current.version ≠ expected) :
    installStyle (E := E) style.base current expected after = (current, .error .stale) :=
  installStyle_stale style.base current expected after stale

/-- Five presentations, with receiver cases reusing the same two base policies. -/
inductive TablePresentation where
  | passing (style : TableStyle)
  | receiver (style : ReceiverStyle)
  deriving DecidableEq, Repr

/-- Representation erasure leaves the existing ownership semantics unchanged. -/
def TablePresentation.base : TablePresentation → TableStyle
  | .passing style => style
  | .receiver style => style.base

/-- Transfer prepares the entire target before retiring an owned source. The
preparation function includes admission and receiver construction in Gerbil. -/
def prepareStyleConvert (source : TablePresentation) (state : Option A)
    (prepare : A → Except E R) : Option A × Except (StyleFailure E) R :=
  match state with
  | none => (none, .error .consumed)
  | some value =>
    match prepare value with
    | .error cause => (state, .error (.callback cause))
    | .ok result => (if source.base = .pure then state else none, .ok result)

/-- The complete five-by-five conversion matrix retains the exact value and tag. -/
theorem presentation_conversion (source target : TablePresentation) (value : A) :
    prepareStyleConvert (E := E) source (some value) (fun payload => .ok (target, payload)) =
      (if source.base = .pure then some value else none, .ok (target, value)) := rfl

/-- Refused conversion leaves every source presentation usable for explicit retry. -/
theorem presentation_conversion_refused (source : TablePresentation) (value : A)
    (prepare : A → Except E R) (cause : E) (refused : prepare value = .error cause) :
    prepareStyleConvert source (some value) prepare =
      (some value, .error (.callback cause)) := by simp [prepareStyleConvert, refused]

/-- Retired aliases cannot invoke target preparation or revive a prior generation. -/
theorem presentation_conversion_retired (source : TablePresentation) (prepare : A → Except E R) :
    prepareStyleConvert source none prepare = (none, .error .consumed) := rfl

/-- Erasing receiver tags agrees with all earlier interface-passing conversions. -/
theorem presentation_conversion_erasure (source target : TablePresentation) (value : A) :
    prepareStyleConvert (E := E) source (some value) (fun payload => .ok (target.base, payload)) =
      styleConvert source.base target.base (some value) := rfl

end LeanPoo.Functional.OrderedDictionary
