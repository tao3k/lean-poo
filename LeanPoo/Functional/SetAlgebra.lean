import LeanPoo.Functional.TableStyle

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

end LeanPoo.Functional.OrderedDictionary
