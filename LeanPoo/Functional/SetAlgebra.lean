import LeanPoo.Functional.TableStyle
import LeanPoo.Functional.TableIndex
import LeanPoo.Functional.TableProjection

/-! Finite set algebra is an additional layer over existing Unit-valued tables.
Backend merge/lookup and persistent write laws remain explicit premises. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- A set view observes membership without requiring key or Function equality. -/
abbrev Membership (K : Type) := K → Bool

/-- The four operations use the same Boolean decision at each backend merge key. -/
inductive SetOperation where
  | union | inter | diff | symdiff
  deriving DecidableEq, Repr

/-- Optional Unit merge is exactly Boolean membership, with no new stored values. -/
def SetOperation.choose : SetOperation → Bool → Bool → Bool
  | .union, a, b => a || b
  | .inter, a, b => a && b
  | .diff, a, b => a && !b
  | .symdiff, a, b => xor a b

/-- The shared table resolver specializes exactly to all four Unit-valued Set
operations, including absent/absent suppression. -/
theorem tableCombination_unit (operation : SetOperation)
    (left right : K → Option Unit) (key : K) :
    (tableCombinationView (fun _ a b =>
      if operation.choose a.isSome b.isSome then some () else none) left right key).isSome =
      operation.choose (left key).isSome (right key).isSome := by
  cases operation <;> cases hl : left key <;> cases hr : right key <;>
    simp [tableCombinationView, hl, hr, SetOperation.choose]

/-- Pointwise semantics does not impose a new enumeration or comparison order. -/
def combineSet (operation : SetOperation) (left right : Membership K) : Membership K :=
  fun key => operation.choose (left key) (right key)

/-- Absence is none; membership stores the existing Unit payload. -/
def membershipTable (view : Membership K) : K → Option Unit :=
  fun key => if view key then some () else none

/-- Lift the existing backend merge selector, preserving the original Unit option. -/
def chooseSetBinding (operation : SetOperation) (left right : Option Unit) : Option Unit :=
  if operation.choose left.isSome right.isSome then
    match left with
    | some value => some value
    | none => right
  else none

/-- All four selectors refine the set laws even at the neither-present branch. -/
theorem chooseSetBinding_membership (operation : SetOperation) (left right : Bool) :
    chooseSetBinding operation (if left then some () else none) (if right then some () else none) =
      if operation.choose left right then some () else none := by
  cases operation <;> cases left <;> cases right <;> rfl

/-- One backend merge law suffices for union, intersection, difference and xor. -/
theorem set_merge_refines (operation : SetOperation) (left right : Membership K)
    (result : K → Option Unit)
    (mergeLaw : ∀ key, result key =
      chooseSetBinding operation (membershipTable left key) (membershipTable right key)) :
    result = membershipTable (combineSet operation left right) := by
  funext key
  rw [mergeLaw]
  exact chooseSetBinding_membership operation (left key) (right key)

/-- Subset is only a membership implication; no payload equality operation is used. -/
def setSubset (left right : Membership K) : Prop := ∀ key, left key = true → right key = true

/-- Disjointness checks no element belongs to both operands. -/
def setDisjoint (left right : Membership K) : Prop := ∀ key, left key = true → right key = false

/-- Finite backend enumeration is complete for the left membership domain. -/
theorem subset_finite (keys : List K) (left right : Membership K)
    (covered : ∀ key, left key = true → key ∈ keys) :
    keys.all (fun key => !left key || right key) = true ↔ setSubset left right := by
  simp only [List.all_eq_true]
  constructor
  · intro h key member
    have atKey := h key (covered key member)
    simpa [member] using atKey
  · intro h key _
    cases atKey : left key
    · simp [atKey]
    · simp [atKey, h key atKey]

/-- Short-circuit disjointness is complete over the same finite left inventory. -/
theorem disjoint_finite (keys : List K) (left right : Membership K)
    (covered : ∀ key, left key = true → key ∈ keys) :
    keys.all (fun key => !(left key && right key)) = true ↔ setDisjoint left right := by
  simp only [List.all_eq_true]
  constructor
  · intro h key member
    have atKey := h key (covered key member)
    simpa [member] using atKey
  · intro h key _
    cases atKey : left key
    · simp [atKey]
    · simp [atKey, h key atKey]

/-- Mutual subset gives extensional equality without comparing Function keys. -/
theorem set_equal_iff (left right : Membership K) :
    (setSubset left right ∧ setSubset right left) ↔ left = right := by
  constructor
  · intro ⟨forward, backward⟩
    funext key
    cases a : left key <;> cases b : right key <;> simp_all [setSubset]
  · intro h
    subst right
    exact ⟨fun _ h => h, fun _ h => h⟩

/-- Membership complement relative to the left operand is ordinary difference. -/
theorem set_diff_partition (left right : Membership K) :
    combineSet .union (combineSet .inter left right) (combineSet .diff left right) = left := by
  funext key
  cases a : left key <;> cases b : right key <;> simp [combineSet, SetOperation.choose, a, b]

/-- Shared elements are removed by symmetric difference, including identical sets. -/
theorem set_symdiff_self (view : Membership K) :
    combineSet .symdiff view view = fun _ => false := by
  funext key
  cases h : view key <;> simp [combineSet, SetOperation.choose, h]

/-- Revocation wins after a grant in the access-policy example. -/
theorem set_revocation_wins (current grants revoked : Membership K) (key : K)
    (denied : revoked key = true) :
    combineSet .diff (combineSet .union current grants) revoked key = false := by
  simp [combineSet, SetOperation.choose, denied]

/-- Ordinary table deltas install a finite algebra result with the same first-key
conflict and inverse semantics as every other persistent table. -/
theorem set_revision_complete [DecidableEq K] (operation : SetOperation)
    (keys : List K) (unique : keys.Nodup) (before right : Membership K)
    (covered : ∀ key, key ∉ keys → before key = combineSet operation before right key) :
    applyChanges (diffChanges keys (membershipTable before)
      (membershipTable (combineSet operation before right))) (membershipTable before) =
        .ok (membershipTable (combineSet operation before right)) := by
  apply diff_complete keys unique
  intro key outside
  simp [membershipTable, covered key outside]

/-- Inverse recovery delegates to the existing whole-delta theorem. -/
theorem set_revision_inverse [DecidableEq K] (changes : List (Change K Unit))
    (before after : Membership K)
    (installed : applyChanges changes (membershipTable before) = .ok (membershipTable after)) :
    applyChanges (inverseChanges changes) (membershipTable after) = .ok (membershipTable before) :=
  applyChanges_inverse changes _ _ installed

/-- Boolean membership focus reuses the existing optional-write operation. -/
def setMembership (view : Membership K) (key : K) [DecidableEq K] (present : Bool) : Membership K :=
  fun query => if query = key then present else view query

/-- The corrected value-before-state setter satisfies all three project lens laws. -/
theorem set_membership_lens [DecidableEq K] (key : K) :
    LeanPoo.Prototype.LensLaws (fun view : Membership K => view key)
      (fun present view => setMembership view key present) := by
  constructor
  · intro view
    funext query
    by_cases h : query = key <;> simp_all [setMembership]
  · intro view present
    simp [setMembership]
  · intro view first second
    funext query
    by_cases h : query = key <;> simp [setMembership, h]

/-- Both commutative merges preserve exactly the same memberships. -/
theorem set_union_comm (left right : Membership K) :
    combineSet .union left right = combineSet .union right left := by
  funext key
  cases a : left key <;> cases b : right key <;> simp [combineSet, SetOperation.choose, a, b]

/-- Intersection order changes no membership; backend enumeration may still differ. -/
theorem set_inter_comm (left right : Membership K) :
    combineSet .inter left right = combineSet .inter right left := by
  funext key
  cases a : left key <;> cases b : right key <;> simp [combineSet, SetOperation.choose, a, b]

/-- Repeated union never creates duplicate logical elements. -/
theorem set_union_idempotent (view : Membership K) : combineSet .union view view = view := by
  funext key
  cases h : view key <;> simp [combineSet, SetOperation.choose, h]

/-- Difference removes every common element, including the identical-set case. -/
theorem set_diff_self (view : Membership K) : combineSet .diff view view = fun _ => false := by
  funext key
  cases h : view key <;> simp [combineSet, SetOperation.choose, h]

/-- Subset composition does not require a key comparator or finite universe. -/
theorem setSubset_trans (left middle right : Membership K)
    (first : setSubset left middle) (second : setSubset middle right) : setSubset left right :=
  fun key member => second key (first key member)

/-- Disjointness is symmetric even when the backend chooses a traversal direction. -/
theorem setDisjoint_symm (left right : Membership K) (apart : setDisjoint left right) :
    setDisjoint right left := by
  intro key member
  cases h : left key
  · rfl
  · have contradiction := apart key h
    rw [member] at contradiction
    contradiction

/-- Membership focus is exactly the existing Unit-valued optional table write. -/
theorem membershipTable_setMembership [DecidableEq K] (view : Membership K) (key : K) (present : Bool) :
    membershipTable (setMembership view key present) =
      replace (membershipTable view) key (if present then some () else none) := by
  funext query
  by_cases h : query = key <;> simp [membershipTable, setMembership, replace, h]

/-- Admission for the concrete set protocol: every input precedes construction,
then the complete successor is recognized once before publication. The recognizer
combines backing carrier/child checks and the declared set refinement. -/
def admitSetOperation (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) : Except E A :=
  (inputs.mapM admit).bind fun _ =>
    (construct ()).bind fun root => (admit root).map fun _ => root

/-- An input refusal suppresses construction and preserves the exact cause. -/
theorem admitSetOperation_inputs_refused (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) (cause : E)
    (refused : inputs.mapM admit = .error cause) :
    admitSetOperation inputs admit construct = .error cause := by
  simp [admitSetOperation, refused, Except.bind]

/-- A backend refusal cannot be replaced by a later root-recognizer failure. -/
theorem admitSetOperation_build_refused (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) (checks : List Unit) (cause : E)
    (accepted : inputs.mapM admit = .ok checks) (refused : construct () = .error cause) :
    admitSetOperation inputs admit construct = .error cause := by
  simp [admitSetOperation, accepted, refused, Except.bind]

/-- Valid inputs do not imply an arbitrary refinement is closed under union or
any other algebra operation. Final admission remains a separate obligation. -/
theorem admitSetOperation_final_refused (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) (checks : List Unit) (root : A) (cause : E)
    (accepted : inputs.mapM admit = .ok checks) (built : construct () = .ok root)
    (refused : admit root = .error cause) :
    admitSetOperation inputs admit construct = .error cause := by
  simp [admitSetOperation, accepted, built, refused, Except.bind, Except.map]

/-- A successful complete constructor publishes its exact root, never a normalized
copy. No hypothesis requires the constructor's private intermediate roots. -/
theorem admitSetOperation_ready (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) (checks : List Unit) (root : A)
    (accepted : inputs.mapM admit = .ok checks) (built : construct () = .ok root)
    (checked : admit root = .ok ()) :
    admitSetOperation inputs admit construct = .ok root := by
  simp [admitSetOperation, accepted, built, checked, Except.bind, Except.map]

/-- Faithful recognition establishes both carrier laws and the declared set
refinement for every published root, independent of backend representation. -/
theorem admitSetOperation_valid (inputs : List A) (admit : A → Except E Unit)
    (construct : Unit → Except E A) (Valid : A → Prop)
    (faithful : ∀ root, admit root = .ok () → Valid root) (root : A)
    (published : admitSetOperation inputs admit construct = .ok root) : Valid root := by
  cases hi : inputs.mapM admit with
  | error cause => simp [admitSetOperation, hi, Except.bind] at published
  | ok checks =>
    cases hb : construct () with
    | error cause => simp [admitSetOperation, hi, hb, Except.bind] at published
    | ok result =>
      cases ha : admit result with
      | error cause => simp [admitSetOperation, hi, hb, ha, Except.bind, Except.map] at published
      | ok checkedUnit =>
        cases checkedUnit
        have same : result = root := by
          simpa [admitSetOperation, hi, hb, ha, Except.bind, Except.map] using published
        subst root
        exact faithful result ha

/-- Partial refinements retain the ordinary membership lens observation law on
accepted writes. A refused membership change is not silently weakened. -/
theorem admitted_set_membership [DecidableEq K] (view : Membership K) (key : K)
    (present : Bool) (admit : Membership K → Except E Unit)
    (accepted : admit view = .ok ()) (checked : admit (setMembership view key present) = .ok ()) :
    (admitSetOperation [view] admit (fun _ => .ok (setMembership view key present))).map
      (fun after => after key) = .ok present := by
  simp [admitSetOperation, accepted, checked, List.mapM_cons, Except.bind, Except.map]
  change Except.ok (setMembership view key present key) = Except.ok present
  simp [setMembership]

/-- For an arity-admitted argument row, the shared method boundary checks original
roots and recognizes the element arguments,
then resolves the delegate and admits its complete result. Recognition need not
normalize stored Function leaves; lookup remains after both input phases. -/
def admitSetMethod (roots : List A) (admit : A → Except E Unit)
    (args : Args) (recognize : Args → Except E Args)
    (resolve : Unit → Except E (Args → Except E A)) : Except E A :=
  admitSetOperation roots admit fun _ =>
    (recognize args).bind fun checked =>
      (resolve ()).bind fun method => method checked

/-- Recognition-only argument checks and successful delegate resolution preserve
exactly the previous operation semantics, including every final refusal. -/
theorem admitSetMethod_delegation (roots : List A) (admit : A → Except E Unit)
    (args : Args) (recognize : Args → Except E Args)
    (resolve : Unit → Except E (Args → Except E A)) (method : Args → Except E A)
    (recognized : recognize args = .ok args) (resolved : resolve () = .ok method) :
    admitSetMethod roots admit args recognize resolve =
      admitSetOperation roots admit (fun _ => method args) := by
  simp [admitSetMethod, recognized, resolved, Except.bind]

/-- Original-root refusal suppresses argument predicates and delegate lookup. -/
theorem admitSetMethod_roots_refused (roots : List A) (admit : A → Except E Unit)
    (args : Args) (recognize : Args → Except E Args)
    (resolve : Unit → Except E (Args → Except E A)) (cause : E)
    (refused : roots.mapM admit = .error cause) :
    admitSetMethod roots admit args recognize resolve = .error cause := by
  simp [admitSetMethod, admitSetOperation, refused, Except.bind]

/-- A refused element argument row suppresses lookup and result admission;
its original cause is retained even if the delegate would also fail. -/
theorem admitSetMethod_arguments_refused (roots : List A) (admit : A → Except E Unit)
    (args : Args) (recognize : Args → Except E Args)
    (resolve : Unit → Except E (Args → Except E A)) (checks : List Unit) (cause : E)
    (accepted : roots.mapM admit = .ok checks) (refused : recognize args = .error cause) :
    admitSetMethod roots admit args recognize resolve = .error cause := by
  simp [admitSetMethod, admitSetOperation, accepted, refused, Except.bind]

/-- Every successful family method satisfies the same faithful Set recognizer;
introducing a method family cannot bypass final validation. -/
theorem admitSetMethod_valid (roots : List A) (admit : A → Except E Unit)
    (args : Args) (recognize : Args → Except E Args)
    (resolve : Unit → Except E (Args → Except E A)) (Valid : A → Prop)
    (faithful : ∀ root, admit root = .ok () → Valid root) (root : A)
    (published : admitSetMethod roots admit args recognize resolve = .ok root) : Valid root :=
  admitSetOperation_valid roots admit _ Valid faithful root published

/-- Image membership observes grouped owners, never a unique-owner projection.
Logical keys are backend equality classes; the finite inventory covers live owners. -/
def setImage (owners : List K) (groups : I → K → Option Unit) (bucket : I) : Bool :=
  owners.any (fun key => (groups bucket key).isSome)

/-- Deduplication has exactly the existential witness semantics of a Set image. -/
theorem setImage_present (owners : List K) (groups : I → K → Option Unit) (bucket : I) :
    setImage owners groups bucket = true ↔
      ∃ key ∈ owners, (groups bucket key).isSome = true := by
  simp [setImage, List.any_eq_true]

/-- A grouped image is precisely the mathematical image of the admitted source,
restricted to the explicit finite inventory; Unit stores no extra payload. -/
theorem setImage_grouped_iff [DecidableEq I] (owners : List K)
    (project : K → Unit → I) (primary : K → Option Unit) (bucket : I) :
    setImage owners (indexView project primary) bucket = true ↔
      ∃ key ∈ owners, primary key = some () ∧ project key () = bucket := by
  rw [setImage_present]
  constructor
  · rintro ⟨key, listed, live⟩
    cases h : primary key with
    | none => simp [indexView, h] at live
    | some value =>
      cases value
      exact ⟨key, listed, h, by simpa [indexView, h] using live⟩
  · rintro ⟨key, listed, present, projected⟩
    exact ⟨key, listed, by simp [indexView, present, projected]⟩

/-- A finite multivalued image is the union of all live owners' declared
memberships. Duplicate outputs do not confer additional ownership. -/
theorem setImage_keys_iff [DecidableEq I] (owners : List K)
    (project : K → Unit → List I) (primary : K → Option Unit) (bucket : I) :
    setImage owners (indexKeysView project primary) bucket = true ↔
      ∃ key ∈ owners, primary key = some () ∧ bucket ∈ project key () := by
  rw [setImage_present]
  constructor
  · rintro ⟨key, listed, live⟩
    cases h : primary key with
    | none => simp [indexKeysView, h] at live
    | some value =>
      cases value
      exact ⟨key, listed, h, by simpa [indexKeysView, h] using live⟩
  · rintro ⟨key, listed, present, projected⟩
    exact ⟨key, listed, by simp [indexKeysView, present, projected]⟩

/-- Single-output and finite-output cardinalities share one image semantics;
a list-valued single key is distinct from a declared list of keys. -/
theorem setImage_keys_singleton [DecidableEq I] (owners : List K)
    (project : K → Unit → I) (primary : K → Option Unit) :
    setImage owners (indexKeysView (fun key row => [project key row]) primary) =
      setImage owners (indexView project primary) := by
  congr 1
  funext bucket key
  cases h : primary key <;> simp [indexKeysView, indexView, h, eq_comm]

/-- Duplicating every finite output does not change target observations or
introduce a second reference to normalize an opaque Function key. -/
theorem setImage_keys_duplicate [DecidableEq K] [DecidableEq I] (owners : List K) (project : K → Unit → List I)
    (primary : K → Option Unit) :
    setImage owners (indexKeysView (fun key row => project key row ++ project key row) primary) =
      setImage owners (indexKeysView project primary) := by
  rw [indexKeysView_duplicate]

/-- A live owner may contribute no keys, without an invented sentinel element. -/
theorem setImage_keys_empty [DecidableEq I] (owners : List K) (primary : K → Option Unit) (bucket : I) :
    setImage owners (indexKeysView (fun _ _ => []) primary) bucket = false := by
  simp only [setImage, List.any_eq_false]
  intro key _listed
  cases h : primary key <;> simp [indexKeysView, h]

/-- Selective multikey index repair yields exactly a complete finite flattening,
using the existing source frame. It does not scan unrelated source columns. -/
theorem setImage_keys_revise [DecidableEq K] [DecidableEq I] (owners keys : List K)
    (project : K → Unit → List I) (before after : K → Option Unit)
    (frame : ∀ key, key ∉ keys → after key = before key) :
    setImage owners (reviseIndexKeys keys project after (indexKeysView project before)) =
      setImage owners (indexKeysView project after) := by
  rw [reviseIndexKeys_correct keys project before after frame]

/-- Existing source delta conflicts and frame discipline suffice to repair the
whole finite-output image. Backend costs and recognizers are separate premises. -/
theorem setImage_keys_delta [DecidableEq K] [DecidableEq I] (owners : List K)
    (ops : TableCarrier K Unit A) (project : K → Unit → List I)
    (edits : List (Change K Unit)) (before after : A)
    (ready : ops.apply edits before = .ok after) :
    setImage owners (reviseIndexKeys (edits.map Change.key) project (ops.read after)
      (indexKeysView project (ops.read before))) =
      setImage owners (indexKeysView project (ops.read after)) := by
  rw [reviseIndexKeys_delta ops project edits before after ready]

/-- Inverting a successful source delta restores the complete multivalued image;
no inverse of the many-to-many relation is needed or inferred. -/
theorem setImage_keys_inverse [DecidableEq K] [DecidableEq I] (owners : List K)
    (project : K → Unit → List I) (edits : List (Change K Unit))
    (before after : K → Option Unit) (ready : applyChanges edits before = .ok after) :
    (applyChanges (inverseChanges edits) after).map
      (fun restored => setImage owners (indexKeysView project restored)) =
      .ok (setImage owners (indexKeysView project before)) := by
  rw [applyChanges_inverse edits before after ready]
  rfl

/-- Deliver one target edit only when owner-bucket occupancy changes. The key
and Unit leaves are exact; unchanged shared buckets emit no replacement. -/
def setImageEdit (bucket : I) (before after : Bool) : List (Change I Unit) :=
  if before = after then [] else
    [⟨bucket, if before then some () else none, if after then some () else none⟩]

/-- Removing a nonlast owner produces zero target writes. -/
theorem setImageEdit_retained (bucket : I) (present : Bool) :
    setImageEdit bucket present present = [] := by simp [setImageEdit]

/-- Last-owner removal carries an exact old membership expectation. -/
theorem setImageEdit_last (bucket : I) :
    setImageEdit bucket true false = [⟨bucket, some (), none⟩] := rfl

/-- Explicit target inversion restores the occupancy transition, including no-op. -/
theorem setImageEdit_inverse (bucket : I) (before after : Bool) :
    inverseChanges (setImageEdit bucket before after) = setImageEdit bucket after before := by
  cases before <;> cases after <;> rfl

/-- Removing one owner cannot erase an image with another surviving witness. -/
theorem setImage_retained (owners : List K) (groups : I → K → Option Unit)
    (bucket : I) (survivor : K) (listed : survivor ∈ owners)
    (live : groups bucket survivor = some ()) : setImage owners groups bucket = true := by
  exact (setImage_present owners groups bucket).mpr ⟨survivor, listed, by simp [live]⟩

/-- A bucket disappears exactly when its complete live-owner inventory is empty. -/
theorem setImage_absent (owners : List K) (groups : I → K → Option Unit) (bucket : I) :
    setImage owners groups bucket = false ↔ ∀ key ∈ owners, groups bucket key = none := by
  simp [setImage, List.any_eq_false, Option.isSome_eq_false_iff]

/-- Selective grouped-index repair gives the same image as complete regrouping.
This uses the existing frame law, not an unproved fresh counting algorithm. -/
theorem setImage_revise [DecidableEq K] [DecidableEq I]
    (owners keys : List K) (project : K → Unit → I) (before after : K → Option Unit)
    (frame : ∀ key, key ∉ keys → after key = before key) (bucket : I) :
    setImage owners (reviseIndex keys project after (indexView project before)) bucket =
      setImage owners (indexView project after) bucket := by
  rw [reviseIndex_correct keys project before after frame]

/-- Successful source edits and their explicit inverse restore the same grouped
image. No inverse of the many-to-one projection itself is asserted. -/
theorem setImage_inverse [DecidableEq K] [DecidableEq I]
    (owners : List K) (project : K → Unit → I) (edits : List (Change K Unit))
    (before after : K → Option Unit) (ready : applyChanges edits before = .ok after) :
    (applyChanges (inverseChanges edits) after).map
      (fun restored => setImage owners (indexView project restored)) =
      .ok (setImage owners (indexView project before)) := by
  rw [applyChanges_inverse edits before after ready]
  rfl

/-- Publishing a prepared image reuses the existing style transaction: target
failure returns no successor and preserves the public owner for retry. -/
theorem setImage_publish_refused (next : S) (delta : D) (style : TableStyle)
    (before : T) (install : T → D → Except E T) (cause : E)
    (refused : install before delta = .error cause) :
    publishProjectionDelivery (.ok (next, delta)) style (some before) install =
      (some before, .error (.callback cause)) :=
  publishProjectionDelivery_install_refused next delta style before install cause refused

/-- A two-input incremental view recomputes only the coalesced edited keys. -/
def reviseSetCombination [DecidableEq K] (keys : List K) (operation : SetOperation)
    (left right cache : Membership K) : Membership K := fun key =>
  if key ∈ keys then operation.choose (left key) (right key) else cache key

/-- Independent source frames imply a frame for every binary Set operation. -/
theorem combineSet_frame (operation : SetOperation)
    (beforeLeft beforeRight afterLeft afterRight : Membership K) (keys : List K)
    (leftFrame : ∀ key, key ∉ keys → afterLeft key = beforeLeft key)
    (rightFrame : ∀ key, key ∉ keys → afterRight key = beforeRight key)
    (key : K) (outside : key ∉ keys) :
    combineSet operation afterLeft afterRight key = combineSet operation beforeLeft beforeRight key := by
  simp only [combineSet, leftFrame key outside, rightFrame key outside]

/-- Changed-key maintenance agrees with a complete binary recomputation. -/
theorem reviseSetCombination_correct [DecidableEq K] (operation : SetOperation)
    (beforeLeft beforeRight afterLeft afterRight : Membership K) (keys : List K)
    (leftFrame : ∀ key, key ∉ keys → afterLeft key = beforeLeft key)
    (rightFrame : ∀ key, key ∉ keys → afterRight key = beforeRight key) :
    reviseSetCombination keys operation afterLeft afterRight
      (combineSet operation beforeLeft beforeRight) = combineSet operation afterLeft afterRight := by
  funext key
  by_cases inside : key ∈ keys
  · simp [reviseSetCombination, combineSet, inside]
  · simp [reviseSetCombination, combineSet, inside, leftFrame key inside, rightFrame key inside]

/-- Duplicate edit occurrences do not change the maintained result; the backend
registry may coalesce by logical key equality without changing source order checks. -/
theorem reviseSetCombination_coalesced [DecidableEq K] (operation : SetOperation)
    (left right cache : Membership K) (raw keys : List K)
    (same : ∀ key, key ∈ raw ↔ key ∈ keys) :
    reviseSetCombination raw operation left right cache =
      reviseSetCombination keys operation left right cache := by
  funext key
  simp only [reviseSetCombination, same key]

/-- The delivered target delta uses only edited keys, yet reconstructs the whole
new combination under the two source frame premises. Full scans are unnecessary. -/
theorem setCombination_delta [DecidableEq K] (operation : SetOperation)
    (beforeLeft beforeRight afterLeft afterRight : Membership K) (keys : List K)
    (unique : keys.Nodup)
    (leftFrame : ∀ key, key ∉ keys → afterLeft key = beforeLeft key)
    (rightFrame : ∀ key, key ∉ keys → afterRight key = beforeRight key) :
    applyChanges (diffChanges keys (membershipTable (combineSet operation beforeLeft beforeRight))
      (membershipTable (combineSet operation afterLeft afterRight)))
      (membershipTable (combineSet operation beforeLeft beforeRight)) =
      .ok (membershipTable (combineSet operation afterLeft afterRight)) := by
  apply diff_complete keys unique
  intro key outside
  simp only [membershipTable, combineSet_frame operation beforeLeft beforeRight
    afterLeft afterRight keys leftFrame rightFrame key outside]

/-- Source ownership can move without a target edit when the binary result agrees. -/
theorem setCombination_noop (operation : SetOperation)
    (beforeLeft beforeRight afterLeft afterRight : Membership K) (keys : List K)
    (same : combineSet operation beforeLeft beforeRight = combineSet operation afterLeft afterRight) :
    diffChanges keys (membershipTable (combineSet operation beforeLeft beforeRight))
      (membershipTable (combineSet operation afterLeft afterRight)) = [] := by
  rw [same]
  simp [diffChanges]

/-- Explicit target inverse edits restore the original complete membership view. -/
theorem setCombination_inverse [DecidableEq K] (edits : List (Change K Unit))
    (before after : Membership K)
    (ready : applyChanges edits (membershipTable before) = .ok (membershipTable after)) :
    applyChanges (inverseChanges edits) (membershipTable after) = .ok (membershipTable before) :=
  applyChanges_inverse edits _ _ ready

/-- Two source installations are staged in order, before any result preparation.
Successful source values remain private until the existing publication gate. -/
def prepareSetCombination (left : Except E L) (right : Except E R)
    (prepare : L → R → Except E A) : Except E A :=
  left.bind fun a => right.bind fun b => prepare a b

/-- Left refusal suppresses the continuation and retains its original cause. -/
theorem prepareSetCombination_left_refused (cause : E) (right : Except E R)
    (prepare : L → R → Except E A) :
    prepareSetCombination (.error cause) right prepare = .error cause := rfl

/-- Right refusal exposes no left successor or target result. -/
theorem prepareSetCombination_right_refused (left : L) (cause : E)
    (prepare : L → R → Except E A) :
    prepareSetCombination (.ok left) (.error cause) prepare = .error cause := rfl

/-- Jointly accepted sources feed the exact existing delivery/publication stage. -/
theorem prepareSetCombination_ready (left : L) (right : R)
    (prepare : L → R → Except E A) :
    prepareSetCombination (.ok left) (.ok right) prepare = prepare left right := rfl

/-- Set reads check the complete original carrier/refinement before resolving an
observation. Results have an independent type; reads do not construct a Set root.
Metadata protection and faithful backend enumeration remain explicit premises. -/
def admitSetRead (root : A) (admit : A → Except E Unit)
    (read : A → Except E R) : Except E R :=
  (admit root).bind fun _ => read root

/-- Refused input suppresses every backend read and callback, retaining its cause. -/
theorem admitSetRead_refused (root : A) (admit : A → Except E Unit)
    (read : A → Except E R) (cause : E) (refused : admit root = .error cause) :
    admitSetRead root admit read = .error cause := by simp [admitSetRead, refused, Except.bind]

/-- Successful admission delegates the exact observation, without cooking leaves. -/
theorem admitSetRead_ready (root : A) (admit : A → Except E Unit)
    (read : A → Except E R) (ready : admit root = .ok ()) :
    admitSetRead root admit read = read root := by simp [admitSetRead, ready, Except.bind]

/-- Backend refusal keeps its original cause, even after successful root admission. -/
theorem admitSetRead_backend_refused (root : A) (admit : A → Except E Unit)
    (read : A → Except E R) (cause : E) (ready : admit root = .ok ())
    (refused : read root = .error cause) :
    admitSetRead root admit read = .error cause := by rw [admitSetRead_ready root admit read ready, refused]

/-- The finite fold uses the existing ordered monadic fold; opaque accumulators
and Function handles need neither equality nor an unrestricted fallback Type. -/
def readSetFold (rows : List K) (admit : List K → Except E Unit)
    (step : K → R → Except E R) (seed : R) : Except E R :=
  admitSetRead rows admit (fun keys => keys.foldlM (fun acc key => step key acc) seed)

/-- No callback or consumer follows root refusal, including for an empty stream. -/
theorem readSetFold_refused (rows : List K) (admit : List K → Except E Unit)
    (step : K → R → Except E R) (seed : R) (consume : R → Except E B)
    (cause : E) (refused : admit rows = .error cause) :
    (readSetFold rows admit step seed).bind consume = .error cause := by
  simp [readSetFold, admitSetRead, refused, Except.bind]

/-- Successful reads retain the backend's exact traversal and failure order. -/
theorem readSetFold_order (rows : List K) (admit : List K → Except E Unit)
    (step : K → R → Except E R) (seed : R) (ready : admit rows = .ok ()) :
    readSetFold rows admit step seed = rows.foldlM (fun acc key => step key acc) seed :=
  admitSetRead_ready rows admit _ ready

/-- Removing Unit payloads commutes with ordered folds, including callback failure.
The same law on reversed backend rows covers the other traversal direction. -/
theorem foldSetBindings_projection (rows : List (K × Unit))
    (step : K → R → Except E R) (seed : R) :
    rows.foldlM (fun acc row => step row.1 acc) seed =
      (rows.map Prod.fst).foldlM (fun acc key => step key acc) seed := by
  induction rows generalizing seed with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.foldlM_cons]
    cases first : step row.1 seed with
    | error cause => rfl
    | ok next => exact ih next

/-- A head callback refusal prevents every suffix callback and later consumer. -/
theorem readSetFold_head_refused (key : K) (rest : List K)
    (admit : List K → Except E Unit) (step : K → R → Except E R) (seed : R)
    (consume : R → Except E B) (cause : E) (ready : admit (key :: rest) = .ok ())
    (refused : step key seed = .error cause) :
    (readSetFold (key :: rest) admit step seed).bind consume = .error cause := by
  rw [readSetFold_order _ admit step seed ready]
  simp only [List.foldlM_cons, refused]
  rfl

end LeanPoo.Functional.OrderedDictionary
