import LeanPoo.Functional.TableStyle
import LeanPoo.Functional.TableBatch

/-! Typed key focuses reuse optional dictionary replacement, checked callbacks and
style ownership. Laws concern observations of persistent finite carriers; no
physical node exclusivity, arbitrary callback rollback or host runtime proof is
claimed. Required focuses have a present-key domain; optional focuses are total. -/
namespace LeanPoo.Functional.OrderedDictionary

variable {K V E : Type} [DecidableEq K]

/-- One capture precedes the modifier; both refusal and success reuse styleStep.
The callback receives the original optional binding, not a reread after effects. -/
def focusModify (style : TableStyle) (state : Option (K → Option V)) (key : K)
    (transform : Option V → Except E (Option V)) :
    Option (K → Option V) × Except (StyleFailure E) (K → Option V) :=
  styleStep style state (fun before =>
    match transform (before key) with
    | .error cause => .error cause
    | .ok value => .ok (replace before key value))

/-- A setter is the constant modifier and takes the replacement before the source. -/
def focusWrite (style : TableStyle) (key : K) (value : Option V)
    (state : Option (K → Option V)) :=
  focusModify (E := E) style state key (fun _ => .ok value)

/-- Required modification refuses an absent binding without invoking transform. -/
def requireFocus (missing : E) (transform : V → Except E V) : Option V → Except E (Option V)
  | none => .error missing
  | some value => match transform value with
    | .error cause => .error cause
    | .ok next => .ok (some next)

/-- All three ordinary pure lens laws already follow from dictionary replacement. -/
theorem focus_optional_laws (key : K) :
    Prototype.LensLaws (fun view : K → Option V => view key)
      (fun value view => replace view key value) := optional_lens key

/-- Every style's successful setter has the same focused observation. -/
theorem focusWrite_get (style : TableStyle) (key : K) (value : Option V) (before : K → Option V) :
    (focusWrite (E := E) style key value (some before)).2 = .ok (replace before key value) := by
  cases style <;> rfl

/-- A focused write preserves every distinct key, including opaque Function leaves. -/
theorem focusWrite_frame (key query : K) (value : Option V) (before : K → Option V)
    (different : query ≠ key) : replace before key value query = before query := by
  simp [replace, different]

/-- Get-put is observation equality for every style, not reference identity. -/
theorem focusWrite_get_put (style : TableStyle) (key : K) (before : K → Option V) :
    (focusWrite (E := E) style key (before key) (some before)).2 = .ok before := by
  rw [focusWrite_get, (focus_optional_laws key).get_put]

/-- Put-get retains absence versus a stored false through Option. -/
theorem focusWrite_put_get (style : TableStyle) (key : K) (value : Option V) (before : K → Option V) :
    (focusWrite (E := E) style key value (some before)).2.map (fun after => after key) = .ok value := by
  rw [focusWrite_get]
  change Except.ok (replace before key value key) = .ok value
  simp [replace]

/-- Repeated replacement has the same whole view as the final replacement alone. -/
theorem focusWrite_put_put (key : K) (first second : Option V) (before : K → Option V) :
    replace (replace before key first) key second = replace before key second :=
  (focus_optional_laws key).put_put before first second

/-- Callback/recognizer failure leaves the original owner and exact cause intact. -/
theorem focusModify_refused (style : TableStyle) (before : K → Option V) (key : K)
    (transform : Option V → Except E (Option V)) (cause : E)
    (refused : transform (before key) = .error cause) :
    focusModify style (some before) key transform = (some before, .error (.callback cause)) := by
  apply styleStep_failure
  simp [refused]

/-- A retired owner refuses without evaluating its modifier. -/
theorem focusModify_consumed (style : TableStyle) (key : K)
    (transform : Option V → Except E (Option V)) :
    focusModify style none key transform = (none, .error .consumed) := rfl

/-- Required absence is a declared failure, never an invented Any/default value. -/
theorem focusModify_required_absent (style : TableStyle) (key : K) (before : K → Option V)
    (missing : E) (transform : V → Except E V) (absent : before key = none) :
    focusModify style (some before) key (requireFocus missing transform) =
      (some before, .error (.callback missing)) := by
  apply focusModify_refused
  simp [absent, requireFocus]

/-- Linear no-op still retires its predecessor; equality of views grants no reuse. -/
theorem focusWrite_linear_retired (key : K) (before : K → Option V) :
    (focusWrite (E := E) .linear key (before key) (some before)).1 = none := rfl

/-- Mutable no-op preserves its observation at the retained identity. -/
theorem focusWrite_mutable_noop (key : K) (before : K → Option V) :
    (focusWrite (E := E) .mutable key (before key) (some before)).1 = some before := by
  change some (replace before key (before key)) = some before
  rw [(focus_optional_laws key).get_put]

/-- Lens composition delegates modification inside the one captured owner update.
A product models a service with an independent frame, not an atomic second owner. -/
def focusServiceModify (style : TableStyle) (state : Option ((K → Option V) × Frame))
    (key : K) (transform : Option V → Except E (Option V)) :=
  styleStep style state (fun before =>
    match transform (before.1 key) with
    | .error cause => .error cause
    | .ok value => .ok (replace before.1 key value, before.2))

/-- Composed successful modification preserves the entire unrelated service frame. -/
theorem focusServiceModify_frame (style : TableStyle) (before : K → Option V) (frame : Frame)
    (key : K) (transform : Option V → Except E (Option V)) (value : Option V)
    (ready : transform (before key) = .ok value) :
    (focusServiceModify style (some (before, frame)) key transform).2 =
      .ok (replace before key value, frame) := by
  cases style <;> simp [focusServiceModify, styleStep, ready]

/-- A modifier prepared from an older generation cannot overwrite a reentrant
or concurrent winner, even when the callback returns a valid replacement. -/
theorem focusInstall_stale (style : TableStyle) (current : TableGeneration (K → Option V))
    (expected : Nat) (before : K → Option V) (key : K) (value : Option V)
    (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected (replace before key value) =
      (current, .error .stale) := installStyle_stale style current expected _ stale

/-- Optional association is not optional replacement: absence retains the original
binding, while a present request retains its exact payload, even a false value. -/
def associateOption (request old : Option V) : Option V :=
  match request with
  | none => old
  | some value => some value

/-- Recognition still runs on an absent request; an identity result is not an
admission shortcut. Source/key admission is a premise of this finite modifier. -/
def admitAssociation (admit : Option V → Except E Unit) (request old : Option V) :
    Except E (Option V) :=
  (admit request).map (fun _ => associateOption request old)

/-- Child refusal retains its exact cause before a useful successor exists. -/
theorem admitAssociation_refused (admit : Option V → Except E Unit)
    (request old : Option V) (cause : E) (refused : admit request = .error cause) :
    admitAssociation admit request old = .error cause := by
  simp [admitAssociation, refused, Except.map]

/-- Successful association delegates to the existing checked focus update. -/
theorem admitAssociation_ready (admit : Option V → Except E Unit)
    (request old : Option V) (ready : admit request = .ok ()) :
    admitAssociation admit request old = .ok (associateOption request old) := by
  simp [admitAssociation, ready, Except.map]

omit [DecidableEq K] in
/-- Absence changes no binding and captures no edit; it is not a read assertion
against future revisions, just like every other unchanged point request. -/
theorem association_absent_changes [DecidableEq V] (before : K → Option V) (key : K) :
    pointChanges before key (associateOption none (before key)) = [] := by
  simp [associateOption, pointChanges]

/-- Captured association applies exactly its focused observation to the full view. -/
theorem association_apply [DecidableEq V] (before : K → Option V) (key : K)
    (request : Option V) :
    applyChanges (pointChanges before key (associateOption request (before key))) before =
      .ok (replace before key (associateOption request (before key))) :=
  pointChanges_apply before key _

/-- Association inherits complete inverse recovery without replaying the request. -/
theorem association_inverse [DecidableEq V] (before : K → Option V) (key : K)
    (request : Option V) :
    applyChanges (inverseChanges (pointChanges before key (associateOption request (before key))))
      (replace before key (associateOption request (before key))) = .ok before :=
  pointChanges_inverse before key _

/-- A changed present request refuses the original conflicting key on another base. -/
theorem association_stale [DecidableEq V] (before current : K → Option V) (key : K)
    (value : V) (changed : before key ≠ some value) (stale : current key ≠ before key) :
    applyChanges (pointChanges before key (associateOption (some value) (before key))) current =
      .error key := pointChanges_stale before current key _ changed stale

/-- The shared point kernel emits at most one edit. Admission, capture, lookup,
backend writes, whole-root recognition and owner preparation remain charged. -/
theorem association_edit_bound [DecidableEq V] (before : K → Option V) (key : K)
    (request : Option V) :
    (pointChanges before key (associateOption request (before key))).length ≤ 1 :=
  pointChanges_length before key _

/-- A refused request, including absent requests, leaves each style's owner live. -/
theorem association_owner_refused (style : TableStyle) (before : K → Option V)
    (key : K) (admit : Option V → Except E Unit) (request : Option V) (cause : E)
    (refused : admit request = .error cause) :
    focusModify style (some before) key (admitAssociation admit request) =
      (some before, .error (.callback cause)) := by
  apply focusModify_refused
  exact admitAssociation_refused admit request (before key) cause refused

/-- An admitted absence returns the identical observation, for every style. -/
theorem association_absent_result (style : TableStyle) (before : K → Option V)
    (key : K) (admit : Option V → Except E Unit) (ready : admit none = .ok ()) :
    (focusModify style (some before) key (admitAssociation admit none)).2 = .ok before := by
  have same := (focus_optional_laws key).get_put before
  simp [focusModify, styleStep, admitAssociation, ready, Except.map, associateOption, same]

/-- Linear success retires the predecessor even when the admitted request is absent. -/
theorem association_absent_linear (before : K → Option V) (key : K)
    (admit : Option V → Except E Unit) (ready : admit none = .ok ()) :
    (focusModify .linear (some before) key (admitAssociation admit none)).1 = none := by
  simp [focusModify, styleStep, admitAssociation, ready, Except.map]

end LeanPoo.Functional.OrderedDictionary
