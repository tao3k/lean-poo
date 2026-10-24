import LeanPoo.Functional.TableRevision

/-! Complete final-root admission for incremental aggregate publication. This is
finite future work for explicit persistent carriers and supplied recognizers. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Stage privately, recognize the final root, then advance the aggregate.
No intermediate root is required to satisfy a whole-table refinement. -/
def admitFoldUpdate (install : Except E T) (admit : T → Except E Unit)
    (advance : T → Except E A) : Except E (T × A) :=
  install.bind fun table => (admit table).bind fun _ => (advance table).map (table, ·)

/-- An installation conflict retains its exact cause and suppresses later phases. -/
theorem admitFoldUpdate_install_refused (admit : T → Except E Unit)
    (advance : T → Except E A) (cause : E) :
    admitFoldUpdate (.error cause) admit advance = .error cause := rfl

/-- Root refusal occurs before aggregate advancement; neither private result escapes. -/
theorem admitFoldUpdate_root_refused (admit : T → Except E Unit)
    (advance : T → Except E A) (table : T) (cause : E)
    (refused : admit table = .error cause) :
    admitFoldUpdate (.ok table) admit advance = .error cause := by
  simp [admitFoldUpdate, refused, Except.bind]

/-- A successful operation preserves the actual admitted root and aggregate. -/
theorem admitFoldUpdate_ready (admit : T → Except E Unit) (advance : T → Except E A)
    (table : T) (value : A) (accepted : admit table = .ok ())
    (advanced : advance table = .ok value) :
    admitFoldUpdate (.ok table) admit advance = .ok (table, value) := by
  simp [admitFoldUpdate, accepted, advanced, Except.bind, Except.map]

/-- Recognition is an explicit premise, not inferred from child membership,
representation correspondence, or a previous root's acceptance. -/
theorem admitFoldUpdate_valid (install : Except E T) (admit : T → Except E Unit)
    (advance : T → Except E A) (Valid : T → Prop)
    (faithful : ∀ root, admit root = .ok () → Valid root) (table : T) (value : A)
    (published : admitFoldUpdate install admit advance = .ok (table, value)) : Valid table := by
  cases hi : install with
  | error cause => simp [admitFoldUpdate, hi, Except.bind] at published
  | ok root =>
    cases ha : admit root with
    | error cause => simp [admitFoldUpdate, hi, ha, Except.bind] at published
    | ok acceptedUnit =>
      cases acceptedUnit
      cases hv : advance root with
      | error cause => simp [admitFoldUpdate, hi, ha, hv, Except.bind, Except.map] at published
      | ok result =>
        simp [admitFoldUpdate, hi, ha, hv, Except.bind, Except.map] at published
        rcases published with ⟨rfl, rfl⟩
        exact faithful root ha

/-- Existing ordered conflicts and exact recognizer causes remain distinguishable.
Sparse contributions are demanded only after the complete successor is admitted. -/
def checkedFold [DecidableEq K] [DecidableEq V]
    (score : K → V → Int) (admit : (K → Option V) → Except E Unit)
    (edits : List (Change K V)) (before : K → Option V) (acc : Int) :
    Except (Sum K E) ((K → Option V) × Int) :=
  admitFoldUpdate ((applyChanges edits before).mapError Sum.inl)
    (fun root => (admit root).mapError Sum.inr)
    (fun _ => .ok (foldChanges score edits acc))

/-- Final recognition and the existing full-fold oracle agree on accepted updates.
The inventory and aggregate law remain explicit, separate from recognition. -/
theorem checkedFold_correct [DecidableEq K] [DecidableEq V]
    (inventory : List K) (unique : inventory.Nodup) (score : K → V → Int)
    (admit : (K → Option V) → Except E Unit) (edits : List (Change K V))
    (covered : ∀ edit ∈ edits, edit.key ∈ inventory) (before after : K → Option V)
    (installed : applyChanges edits before = .ok after) (accepted : admit after = .ok ()) :
    checkedFold score admit edits before (foldView inventory score before) =
      .ok (after, foldView inventory score after) := by
  have correct := foldChanges_correct inventory unique score edits covered before after installed
  simp [checkedFold, installed, accepted, admitFoldUpdate, correct,
    Except.bind, Except.map, Except.mapError]

/-- Inverse recovery requires admission of the recovered original root, rather than
assuming a target constraint follows automatically from bijective child mappings. -/
theorem checkedFold_inverse [DecidableEq K] [DecidableEq V]
    (score : K → V → Int) (admit : (K → Option V) → Except E Unit)
    (edits : List (Change K V)) (before after : K → Option V) (acc : Int)
    (installed : applyChanges edits before = .ok after) (accepted : admit before = .ok ()) :
    checkedFold score admit (inverseChanges edits) after (foldChanges score edits acc) =
      .ok (before, acc) := by
  have inverse := applyChanges_inverse edits before after installed
  simp [checkedFold, inverse, accepted, admitFoldUpdate, foldChanges_inverse,
    Except.bind, Except.map, Except.mapError]

/-- Source fold completion precedes conversion and complete target admission.
The accepted aggregate is reused exactly, without a second aggregate initializer. -/
def admitFoldTransfer (source : Except E (S × A)) (convert : S → Except E T)
    (admit : T → Except E Unit) : Except E (T × A) :=
  source.bind fun result => admitFoldUpdate (convert result.1) admit (fun _ => .ok result.2)

/-- Source failure suppresses target conversion and recognition without changing its cause. -/
theorem admitFoldTransfer_source_refused (convert : S → Except E T)
    (admit : T → Except E Unit) (cause : E) :
    admitFoldTransfer (.error cause : Except E (S × A)) convert admit = .error cause := rfl

/-- Even lawful translated bindings must pass the independent whole-target constraint. -/
theorem admitFoldTransfer_target_refused (source : S) (value : A)
    (convert : S → Except E T) (admit : T → Except E Unit) (target : T) (cause : E)
    (converted : convert source = .ok target) (refused : admit target = .error cause) :
    admitFoldTransfer (.ok (source, value)) convert admit = .error cause := by
  simp [admitFoldTransfer, converted, admitFoldUpdate_root_refused admit _ target cause refused,
    Except.bind]

/-- Accepted translation preserves an opaque aggregate, including checked Functions. -/
theorem admitFoldTransfer_ready (source : S) (value : A)
    (convert : S → Except E T) (admit : T → Except E Unit) (target : T)
    (converted : convert source = .ok target) (accepted : admit target = .ok ()) :
    admitFoldTransfer (.ok (source, value)) convert admit = .ok (target, value) := by
  simp [admitFoldTransfer, converted, admitFoldUpdate, accepted,
    Except.bind, Except.map]

end LeanPoo.Functional.OrderedDictionary
