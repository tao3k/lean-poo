import LeanPoo.Functional.ContainerValidation

/-! Sentinel optionals and dependent typed values, interpreted with pure finite
callbacks. A present branch checks its own child membership; normalization may
produce a sentinel only if that child Type accepts it. Host identity is separate. -/
namespace LeanPoo.Functional.OptionalValidation

/-- The selected child Type must accept its actual normalized result. -/
def gate (member : Value → Bool) (invalid : Error) (checked : Value) : Except Error Unit :=
  if member checked then .ok () else .error invalid

/-- Maybe and OrFalse supply different absent predicates. Absent sources bypass
child structure, normalization and membership; present sources lock the child. -/
def normalize (absent member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid : Error) (source : Value) : Except Error Value :=
  if absent source then .ok source
  else ObjectContract.validateObject shape check (gate member invalid) source

/-- Absence returns exactly the original sentinel without any child operation. -/
theorem absent (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid : Error) (source : Value)
    (none : missing source = true) : normalize missing member shape check invalid source = .ok source := by
  simp [normalize, none]

/-- Present structure failure suppresses normalization and preserves its cause. -/
theorem shape_error (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid error : Error) (source : Value)
    (present : missing source = false) (failed : shape source = .error error) :
    normalize missing member shape check invalid source = .error error := by
  simp [normalize, present, ObjectContract.validateObject, failed, Except.bind]

/-- Present child errors cannot be converted into successful outer absence. -/
theorem child_error (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid error : Error) (source : Value)
    (present : missing source = false) (structural : shape source = .ok ()) (failed : check source = .error error) :
    normalize missing member shape check invalid source = .error error := by
  simp [normalize, present, ObjectContract.validateObject, structural, failed, Except.bind]

/-- The selected child governs even a returned outer sentinel. This deliberately
does not assert that every successful present normalization remains non-sentinel. -/
theorem selected (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid : Error) (source checked : Value)
    (present : missing source = false) (structural : shape source = .ok ()) (called : check source = .ok checked) :
    normalize missing member shape check invalid source = if member checked then .ok checked else .error invalid := by
  cases hm : member checked <;>
    simp [normalize, present, ObjectContract.validateObject, structural, called, gate, hm, Except.bind, Except.map]

/-- Acceptance distinguishes untouched absence from successful selected-child
normalization. No equality or decision procedure for functions is needed. -/
theorem success (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid : Error) (source checked : Value) :
    normalize missing member shape check invalid source = .ok checked ↔
      (missing source = true ∧ source = checked) ∨
      (missing source = false ∧ shape source = .ok () ∧ check source = .ok checked ∧ member checked = true) := by
  cases hm : missing source with
  | true => simp [normalize, hm]
  | false =>
    rw [normalize, hm]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ObjectContract.validateObject_success]
    cases hc : member checked <;> simp [gate, hc]

/-- The existing sentinel protocol admits unchanged absence or child membership.
Maybe supplies void; OrFalse supplies exactly false. The two predicates are not
interchangeable, and no universal fallback Type is inserted. -/
def Admits (absent : Value → Bool) (member : Value → Prop) (value : Value) : Prop :=
  absent value = true ∨ member value

/-- Covariance reuses one fixed sentinel and the child inclusion law. This is the
optional interpretation premise of finite prototype replacement, including
higher-order child contracts when their behavioral inclusion has been supplied. -/
theorem replacement (absent : Value → Bool) (source target : Value → Prop)
    (included : ∀ value, source value → target value) (value : Value)
    (valid : Admits absent source value) : Admits absent target value := by
  rcases valid with missing | present
  · exact .inl missing
  · exact .inr (included value present)

/-- A present accepted normalization belongs to the selected child, even when its
result is an outer sentinel. Child errors never become successful absence. -/
theorem normalized_member (missing member : Value → Bool) (shape : Value → Except Error Unit)
    (check : Value → Except Error Value) (invalid : Error) (source checked : Value)
    (present : missing source = false)
    (accepted : normalize missing member shape check invalid source = .ok checked) : member checked = true := by
  rcases (success missing member shape check invalid source checked).mp accepted with absent | child
  · simp [present] at absent
  · exact child.2.2.2

/-- Dynamic typed values retain the exact descriptor, validate their payload
through that descriptor and install the normalized value. Invalid descriptors gate all payload work. -/
def typed (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue : Error) (source : Descriptor × Value) : Except Error (Descriptor × Value) :=
  if valid source.1 then
    (normalize (fun _ => false) (member source.1) (shape source.1) (check source.1) invalidValue source.2).map
      (source.1, ·)
  else .error invalidType

/-- An invalid carried Type prevents its payload recognizer/validator from running. -/
theorem invalid_type (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue : Error) (source : Descriptor × Value) (bad : valid source.1 = false) :
    typed valid shape member check invalidType invalidValue source = .error invalidType := by
  simp [typed, bad]

/-- Successful typed normalization preserves the exact supplied Type. -/
theorem descriptor_preserved (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue : Error) (source checked : Descriptor × Value)
    (good : typed valid shape member check invalidType invalidValue source = .ok checked) : checked.1 = source.1 := by
  cases hv : valid source.1 with
  | false => simp [typed, hv] at good
  | true =>
    cases hc : normalize (fun _ => false) (member source.1) (shape source.1) (check source.1) invalidValue source.2 with
    | error error => simp [typed, hv, hc, Except.map] at good
    | ok value =>
      have same : (source.1, value) = checked := by simpa [typed, hv, hc, Except.map] using good
      exact (congrArg Prod.fst same).symm

/-- Accepted typed values have a valid carried descriptor and successful shape,
normalization and selected membership on the exact returned payload. -/
theorem typed_requirements (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue : Error) (source checked : Descriptor × Value)
    (good : typed valid shape member check invalidType invalidValue source = .ok checked) :
    valid source.1 = true ∧ shape source.1 source.2 = .ok () ∧
      check source.1 source.2 = .ok checked.2 ∧ member source.1 checked.2 = true := by
  cases hv : valid source.1 with
  | false => simp [typed, hv] at good
  | true =>
    cases hc : normalize (fun _ => false) (member source.1) (shape source.1) (check source.1) invalidValue source.2 with
    | error error => simp [typed, hv, hc, Except.map] at good
    | ok value =>
      have same : (source.1, value) = checked := by simpa [typed, hv, hc, Except.map] using good
      subst checked
      have accepted := (success (fun _ => false) (member source.1) (shape source.1) (check source.1)
        invalidValue source.2 value).mp hc
      simpa [hv] using accepted

/-- A checked typed payload is passed through, including possible Function wrapping. -/
theorem typed_selected (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue : Error) (source : Descriptor × Value) (checked : Value)
    (typeOK : valid source.1 = true) (structural : shape source.1 source.2 = .ok ())
    (called : check source.1 source.2 = .ok checked) (accepted : member source.1 checked = true) :
    typed valid shape member check invalidType invalidValue source = .ok (source.1, checked) := by
  have normalized := selected (fun _ => false) (member source.1) (shape source.1) (check source.1)
    invalidValue source.2 checked rfl structural called
  simp [typed, typeOK, normalized, accepted, Except.map]

/-- A carried child's original error is never replaced by a generic Type error. -/
theorem typed_error (valid : Descriptor → Bool) (shape : Descriptor → Value → Except Error Unit)
    (member : Descriptor → Value → Bool) (check : Descriptor → Value → Except Error Value)
    (invalidType invalidValue error : Error) (source : Descriptor × Value)
    (typeOK : valid source.1 = true) (structural : shape source.1 source.2 = .ok ())
    (failed : check source.1 source.2 = .error error) :
    typed valid shape member check invalidType invalidValue source = .error error := by
  have rejected := child_error (fun _ => false) (member source.1) (shape source.1) (check source.1)
    invalidValue error source.2 rfl structural failed
  simp [typed, typeOK, rejected, Except.map]
/-- Finite catalogs contain exact descriptor tokens. Coverage is readable set
inclusion, not payload subtyping; the host supplies stable, injective identities. -/
def catalogCovers [DecidableEq Descriptor] (source target : List Descriptor) : Bool :=
  source.all fun descriptor => decide (descriptor ∈ target)

/-- Coverage visits every source token; a finite check never invents a target. -/
theorem catalogCovers_sound [DecidableEq Descriptor] (source target : List Descriptor)
    (accepted : catalogCovers source target = true) :
    ∀ descriptor ∈ source, descriptor ∈ target := by
  simpa [catalogCovers, List.all_eq_true] using accepted

/-- An admitted dependent pair retains the descriptor which selects its payload. -/
def CatalogAdmits (catalog : List Descriptor) (member : Descriptor → Value → Prop)
    (value : Descriptor × Value) : Prop := value.1 ∈ catalog ∧ member value.1 value.2

/-- Catalog widening preserves the very same payload obligation, including
higher-order values. No implication between different descriptor predicates is used. -/
theorem catalog_replacement [DecidableEq Descriptor] (source target : List Descriptor)
    (member : Descriptor → Value → Prop) (value : Descriptor × Value)
    (covered : catalogCovers source target = true) (valid : CatalogAdmits source member value) :
    CatalogAdmits target member value :=
  ⟨catalogCovers_sound source target covered value.1 valid.1, valid.2⟩

/-- The existing dependent normalizer owns recursive wrapping; a finite catalog
only supplies its descriptor gate. Membership and child errors keep their order. -/
def catalogTyped [DecidableEq Descriptor] (catalog : List Descriptor)
    (shape : Descriptor → Value → Except Error Unit) (member : Descriptor → Value → Bool)
    (check : Descriptor → Value → Except Error Value) (invalidType invalidValue : Error)
    (source : Descriptor × Value) : Except Error (Descriptor × Value) :=
  typed (fun descriptor => decide (descriptor ∈ catalog)) shape member check invalidType invalidValue source

/-- An unlisted carried descriptor refuses before any dependent payload callback. -/
theorem catalogTyped_missing [DecidableEq Descriptor] (catalog : List Descriptor)
    (shape : Descriptor → Value → Except Error Unit) (member : Descriptor → Value → Bool)
    (check : Descriptor → Value → Except Error Value) (invalidType invalidValue : Error)
    (source : Descriptor × Value) (missing : source.1 ∉ catalog) :
    catalogTyped catalog shape member check invalidType invalidValue source = .error invalidType := by
  simp [catalogTyped, typed, missing]

/-- Successful catalog normalization preserves its token and validates the
normalized payload through that exact token. Host read-currentness is separate. -/
theorem catalogTyped_sound [DecidableEq Descriptor] (catalog : List Descriptor)
    (shape : Descriptor → Value → Except Error Unit) (member : Descriptor → Value → Bool)
    (check : Descriptor → Value → Except Error Value) (invalidType invalidValue : Error)
    (source checked : Descriptor × Value)
    (accepted : catalogTyped catalog shape member check invalidType invalidValue source = .ok checked) :
    checked.1 = source.1 ∧ source.1 ∈ catalog ∧ member source.1 checked.2 = true := by
  have requirements := typed_requirements _ shape member check invalidType invalidValue source checked accepted
  exact ⟨descriptor_preserved _ shape member check invalidType invalidValue source checked accepted,
    of_decide_eq_true requirements.1, requirements.2.2.2⟩

/-- An actual stale-source refusal gates the entire computation. Establishing
that host read replay detects a supported edit is an implementation obligation. -/
theorem catalog_stale (guard : Except Error Unit) (next : Unit → Except Error Artifact)
    (cause : Error) (failed : guard = .error cause) : guard.bind next = .error cause := by
  simp [failed, Except.bind]

/-- A nominal Type token is local to one captured directory. Display names do
not enter identity; a host capture coalesces aliases of the same descriptor. -/
structure CatalogType (Descriptor : Type) where
  scope : Nat
  descriptor : Descriptor
  deriving DecidableEq

/-- Only exact captured identity replaces an opaque Class/Schema token. -/
def catalogIdentity [DecidableEq Descriptor] (source target : CatalogType Descriptor) : Bool :=
  decide (source = target)

/-- Identity inclusion preserves arbitrary actual Schema predicates, without
assuming that Class ancestry or equal printed metadata implies subtyping. -/
theorem catalogIdentity_sound [DecidableEq Descriptor] (source target : CatalogType Descriptor)
    (member : CatalogType Descriptor → Value → Prop) (value : Value)
    (accepted : catalogIdentity source target = true) (valid : member source value) : member target value := by
  have same : source = target := of_decide_eq_true accepted
  simpa [same] using valid

/-- A fresh capture cannot silently reuse tokens from another directory scope. -/
theorem catalogIdentity_scope [DecidableEq Descriptor] (source target : CatalogType Descriptor)
    (different : source.scope ≠ target.scope) : catalogIdentity source target = false := by
  have unequal : source ≠ target := fun same => different (congrArg CatalogType.scope same)
  simp [catalogIdentity, unequal]

/-- Resolve the complete finite name list before source admission. No partial
prefix is returned when a getter, Type admission or final replay refuses. -/
def captureCatalog (resolve : Name → Except Error Descriptor) (names : List Name)
    (admit : List Descriptor → Except Error Unit) : Except Error (List Descriptor) :=
  (Validation.traverse resolve names).bind fun entries => (admit entries).map fun _ => entries

/-- A successful capture consists of exactly the resolved list and its successful
source admission. Getter termination and discovery of external roots are premises. -/
theorem captureCatalog_sound (resolve : Name → Except Error Descriptor) (names : List Name)
    (admit : List Descriptor → Except Error Unit) (entries : List Descriptor)
    (accepted : captureCatalog resolve names admit = .ok entries) :
    Validation.traverse resolve names = .ok entries ∧ admit entries = .ok () := by
  cases resolved : Validation.traverse resolve names with
  | error cause => simp [captureCatalog, resolved, Except.bind] at accepted
  | ok values =>
    cases admitted : admit values with
    | error cause => simp [captureCatalog, resolved, admitted, Except.bind, Except.map] at accepted
    | ok witness =>
      cases witness
      have same : values = entries := by simpa [captureCatalog, resolved, admitted, Except.bind, Except.map] using accepted
      subst values
      exact ⟨rfl, admitted⟩

/-- Failed resolution preserves its cause and suppresses final source admission. -/
theorem captureCatalog_error (resolve : Name → Except Error Descriptor) (names : List Name)
    (admit : List Descriptor → Except Error Unit) (cause : Error)
    (failed : Validation.traverse resolve names = .error cause) :
    captureCatalog resolve names admit = .error cause := by
  simp [captureCatalog, failed, Except.bind]

/-- A successful callback is published only under the same captured source stamp
before and after work. Stamps may encode all declared finite read observations. -/
def catalogCall [DecidableEq Stamp] (captured observed : Stamp)
    (action : Unit → Except Error (Artifact × Stamp)) (stale : Error) : Except Error Artifact :=
  if captured = observed then
    (action ()).bind fun result => if captured = result.2 then .ok result.1 else .error stale
  else .error stale

/-- Old sources prevent the callback, independently of its behavior. -/
theorem catalogCall_stale [DecidableEq Stamp] (captured observed : Stamp)
    (action : Unit → Except Error (Artifact × Stamp)) (stale : Error) (old : captured ≠ observed) :
    catalogCall captured observed action stale = .error stale := by simp [catalogCall, old]

/-- The original callback error wins; a later source check cannot replace it. -/
theorem catalogCall_error [DecidableEq Stamp] (captured observed : Stamp)
    (action : Unit → Except Error (Artifact × Stamp)) (stale cause : Error)
    (current : captured = observed) (failed : action () = .error cause) :
    catalogCall captured observed action stale = .error cause := by
  simp [catalogCall, current, failed, Except.bind]

/-- A metadata edit during successful work prevents publication. Effects already
performed by the callback are not rolled back by this result-level model. -/
theorem catalogCall_changed [DecidableEq Stamp] (captured observed after : Stamp)
    (action : Unit → Except Error (Artifact × Stamp)) (stale : Error) (artifact : Artifact)
    (current : captured = observed) (called : action () = .ok (artifact, after)) (changed : captured ≠ after) :
    catalogCall captured observed action stale = .error stale := by
  subst observed
  simp [catalogCall, called, changed, Except.bind]

/-- Unchanged stamps preserve the original complete normalization program,
including exact returned wrappers and every child error. -/
theorem catalogCall_stable [DecidableEq Stamp] (captured : Stamp)
    (program : Except Error Artifact) (stale : Error) :
    catalogCall captured captured (fun _ => program.map fun value => (value, captured)) stale = program := by
  cases program <;> simp [catalogCall, Except.map, Except.bind]

/-- Accepted artifacts are exactly callback results under unchanged stamps.
Host replay detecting supported mutation is separate from this semantic theorem. -/
theorem catalogCall_sound [DecidableEq Stamp] (captured observed : Stamp)
    (action : Unit → Except Error (Artifact × Stamp)) (stale : Error) (artifact : Artifact)
    (accepted : catalogCall captured observed action stale = .ok artifact) :
    captured = observed ∧ ∃ after, action () = .ok (artifact, after) ∧ captured = after := by
  unfold catalogCall at accepted
  split at accepted
  next current =>
    refine ⟨current, ?_⟩
    cases called : action () with
    | error cause => simp [called, Except.bind] at accepted
    | ok result =>
      rcases result with ⟨value, after⟩
      simp only [called, Except.bind] at accepted
      split at accepted
      next stable =>
        have same : value = artifact := Except.ok.inj accepted
        subst value
        exact ⟨after, rfl, stable⟩
      next unstable => cases accepted
  next old => cases accepted

end LeanPoo.Functional.OptionalValidation
