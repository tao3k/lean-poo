import LeanPoo.Functional.FunctionSignature

/-! Complete finite partitions of ordered Function call languages. Shapes observe
arity and keyword presence only; runtime wire interpretation and effectful Type
recognizers are separate premises. A rest tail has one stationary input Type. -/
namespace LeanPoo.Functional.FunctionSignature

/-- A canonical decoded shape carries no argument values or default computations. -/
def shapeRow (count : Nat) (keys : List Key) : Call Key Unit :=
  ⟨List.replicate count (), keys.map (fun key => (key, ()))⟩

/-- Erasing placeholder keyword values retains precisely the declared keys. -/
@[simp] theorem shapeRow_keys (count : Nat) (keys : List Key) :
    (shapeRow count keys).keywords.map Prod.fst = keys := by
  simp [shapeRow, List.map_map, Function.comp_def]

/-- Value erasure preserves the existing runtime shape judgment exactly. -/
theorem accepts_shapeRow [DecidableEq Key] (signature : Signature Key) (call : Call Key Value) :
    accepts signature (shapeRow call.positional.length (call.keywords.map Prod.fst)) =
      accepts signature call := by
  unfold accepts
  rw [shapeRow_keys]
  simp [shapeRow, List.map_map, Function.comp_def]

/-- Arity partitions stabilize beyond every fixed required/optional prefix.
The representative still has one tail position, so rest Type checks are retained. -/
def representative (ceiling count : Nat) : Nat := min count (ceiling + 1)

/-- Each signature has identical arity admission at its finite representative. -/
theorem accepts_representative [DecidableEq Key] (signature : Signature Key) (ceiling count keys)
    (bound : signature.required + signature.optional ≤ ceiling) :
    accepts signature (shapeRow (representative ceiling count) keys) =
      accepts signature (shapeRow count keys) := by
  have lower : (signature.required ≤ representative ceiling count) ↔ signature.required ≤ count := by
    unfold representative; omega
  have upper : (representative ceiling count ≤ signature.required + signature.optional) ↔
      count ≤ signature.required + signature.optional := by
    unfold representative; omega
  simp [accepts, shapeRow, lower, upper]

/-- Ordered first-match selection is unchanged when every acceptance bit agrees. -/
theorem select_congr_calls [DecidableEq Key] (signatures : List (Signature Key))
    (left : Call Key A) (right : Call Key B)
    (same : ∀ signature ∈ signatures, accepts signature left = accepts signature right) :
    select signatures left = select signatures right := by
  induction signatures with
  | nil => rfl
  | cons head tail ih =>
    simp only [select, List.find?_cons]
    rw [same head (by simp)]
    split
    · rfl
    · exact ih (fun signature member => same signature (by simp [member]))

/-- The representative preserves the original selected clause, including shadowing. -/
theorem select_representative [DecidableEq Key] (signatures : List (Signature Key)) (ceiling count keys)
    (bounded : ∀ signature ∈ signatures, signature.required + signature.optional ≤ ceiling) :
    select signatures (shapeRow (representative ceiling count) keys) =
      select signatures (shapeRow count keys) :=
  select_congr_calls _ _ _ (fun signature member => accepts_representative _ _ _ _ (bounded signature member))

/-- Enumerate keyword presence masks in declaration order. The Scheme traversal
streams this recursion under its shared quota rather than materializing the list. -/
def keySubsets : List Key → List (List Key)
  | [] => [[]]
  | head :: tail => let rest := keySubsets tail; rest ++ rest.map (head :: ·)

/-- Every presence mask belongs to the enumeration; this is not random sampling. -/
theorem keySubsets_filter [DecidableEq Key] (keyUniverse actual : List Key) :
    keyUniverse.filter (fun key => decide (key ∈ actual)) ∈ keySubsets keyUniverse := by
  induction keyUniverse with
  | nil => simp [keySubsets]
  | cons head tail ih =>
    by_cases present : head ∈ actual
    · simp only [List.filter_cons, decide_eq_true present, ↓reduceIte, keySubsets]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
    · simpa [keySubsets, present] using List.mem_append_left
        ((keySubsets tail).map (head :: ·)) ih

/-- Canonical masks preserve membership when the supplied keys are in the universe. -/
theorem mask_membership [DecidableEq Key] (keyUniverse actual : List Key)
    (inside : ∀ key ∈ actual, key ∈ keyUniverse) (key : Key) :
    key ∈ keyUniverse.filter (fun key => decide (key ∈ actual)) ↔ key ∈ actual := by
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun member => ⟨inside key member, member⟩⟩

/-- Keyword shape checks observe a duplicate-free set, not its wire order. This
law says nothing about evaluation order of user recognizers or other effects. -/
theorem accepts_keys [DecidableEq Key] (signature : Signature Key) (count : Nat)
    (left right : List Key) (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (same : ∀ key, key ∈ left ↔ key ∈ right) :
    accepts signature (shapeRow count left) = accepts signature (shapeRow count right) := by
  have allowed : (∀ key ∈ left, key ∈ signature.keywords) ↔
      (∀ key ∈ right, key ∈ signature.keywords) := by
    constructor
    · intro h key member; exact h key ((same key).mpr member)
    · intro h key member; exact h key ((same key).mp member)
  have required : (∀ key ∈ signature.requiredKeywords, key ∈ left) ↔
      (∀ key ∈ signature.requiredKeywords, key ∈ right) := by
    constructor
    · intro h key member; exact (same key).mp (h key member)
    · intro h key member; exact (same key).mpr (h key member)
  apply Bool.eq_iff_iff.mpr
  unfold accepts
  rw [shapeRow_keys, shapeRow_keys]
  simp [shapeRow, leftUnique, rightUnique, List.all_eq_true, allowed, required]

/-- The actual finite cells cover all arity regions and every keyword mask. -/
def callCells (ceiling : Nat) (keyUniverse : List Key) : List (Call Key Unit) :=
  (List.range (ceiling + 2)).flatMap fun count => (keySubsets keyUniverse).map (shapeRow count)

/-- Every canonicalized call has an actual cell in the finite enumeration. -/
theorem representative_mem [DecidableEq Key] (ceiling count : Nat) (keyUniverse actual : List Key) :
    shapeRow (representative ceiling count) (keyUniverse.filter (fun key => decide (key ∈ actual))) ∈
      callCells ceiling keyUniverse := by
  apply List.mem_flatMap.mpr
  refine ⟨representative ceiling count, ?_, ?_⟩
  · simp only [List.mem_range, representative]; omega
  · exact List.mem_map.mpr ⟨_, keySubsets_filter keyUniverse actual, rfl⟩

/-- Decidable ordered language inclusion checks selected clauses at every cell.
`related` also checks variance/results in the typed version; pure coverage uses true. -/
def coversCalls [DecidableEq Key] (cells : List (Call Key Unit)) (source target : List (Signature Key))
    (related : Signature Key → Signature Key → Call Key Unit → Bool) : Bool :=
  cells.all fun row => match select target row with
    | none => true
    | some expected => match select source row with
      | none => false
      | some actual => related actual expected row

/-- A certificate retains the actual first selected pair for every covered cell. -/
theorem coversCalls_cell [DecidableEq Key] (cells : List (Call Key Unit)) (source target)
    (related) (covered : coversCalls cells source target related = true)
    (row) (member : row ∈ cells) (expected) (selected : select target row = some expected) :
    ∃ actual, select source row = some actual ∧ related actual expected row = true := by
  have valid := (List.all_eq_true.mp covered) row member
  simp only [selected] at valid
  cases found : select source row with
  | none => simp [found] at valid
  | some actual => exact ⟨actual, rfl, by simpa [found] using valid⟩

/-- A truly universal selected-clause coverage relation passes every finite cell.
Together with soundness this establishes exact shape coverage in the shared
wire domain, rather than an under-approximation from observed call examples. -/
theorem coversCalls_complete [DecidableEq Key] (cells : List (Call Key Unit))
    (source target : List (Signature Key))
    (every : ∀ (row : Call Key Unit) expected, select target row = some expected → ∃ actual, select source row = some actual) :
    coversCalls cells source target (fun _ _ _ => true) = true := by
  apply List.all_eq_true.mpr
  intro row _
  cases selected : select target row with
  | none => simp
  | some expected =>
    obtain ⟨actual, found⟩ := every row expected selected
    simp [found]

/-- All duplicate-free decoded calls in the target key universe are covered.
The finite proof preserves first selection and includes unbounded rest arities. -/
theorem coversCalls_sound [DecidableEq Key] (ceiling : Nat) (keyUniverse : List Key)
    (unique : keyUniverse.Nodup) (source target : List (Signature Key))
    (bounded : ∀ signature ∈ source ++ target, signature.required + signature.optional ≤ ceiling)
    (covered : coversCalls (callCells ceiling keyUniverse) source target (fun _ _ _ => true) = true)
    (count : Nat) (keys : List Key) (keysUnique : keys.Nodup)
    (inside : ∀ key ∈ keys, key ∈ keyUniverse) (expected)
    (selected : select target (shapeRow count keys) = some expected) :
    ∃ actual, select source (shapeRow count keys) = some actual := by
  let mask := keyUniverse.filter (fun key => decide (key ∈ keys))
  have maskUnique : mask.Nodup := unique.filter _
  have keyEqual : ∀ signature : Signature Key,
      accepts signature (shapeRow count mask) = accepts signature (shapeRow count keys) :=
    fun signature => accepts_keys signature count _ _ maskUnique keysUnique (mask_membership _ _ inside)
  have transport : ∀ signatures : List (Signature Key),
      (∀ signature ∈ signatures, signature.required + signature.optional ≤ ceiling) →
      select signatures (shapeRow (representative ceiling count) mask) = select signatures (shapeRow count keys) := by
    intro signatures small
    rw [select_representative signatures ceiling count mask small]
    exact select_congr_calls _ _ _ (fun signature _ => keyEqual signature)
  have left := transport source (fun s m => bounded s (List.mem_append_left _ m))
  have right := transport target (fun s m => bounded s (List.mem_append_right _ m))
  obtain ⟨actual, found, _⟩ := coversCalls_cell _ _ _ _ covered _
    (representative_mem ceiling count keyUniverse keys) expected (right.trans selected)
  exact ⟨actual, left.symm.trans found⟩

/-- Positional Types use the declared fixed prefix, then the one rest Type. -/
def TypedSignature.inputAt (signature : TypedSignature Key Ty) (index : Nat) : Option Ty :=
  ((signature.inputs ++ signature.optional)[index]?).or signature.rest

/-- Past the fixed prefix, every tail position has exactly the same Type. -/
theorem inputAt_tail (signature : TypedSignature Key Ty) (index : Nat)
    (beyond : (signature.inputs ++ signature.optional).length ≤ index) :
    signature.inputAt index = signature.rest := by
  simp [TypedSignature.inputAt, List.getElem?_eq_none beyond]

/-- A positional relation checked at the finite representative lifts to every
position of a longer supplied row. This proves why the extra rest cell is needed. -/
theorem inputAt_representative (ceiling count : Nat)
    (source target : TypedSignature Key Ty) (relation : Option Ty → Option Ty → Prop)
    (left : (source.inputs ++ source.optional).length ≤ ceiling)
    (right : (target.inputs ++ target.optional).length ≤ ceiling)
    (checked : ∀ index < representative ceiling count, relation (target.inputAt index) (source.inputAt index)) :
    ∀ index < count, relation (target.inputAt index) (source.inputAt index) := by
  intro index member
  by_cases small : index < representative ceiling count
  · exact checked index small
  · have large : ceiling < count := by unfold representative at small; omega
    have tailIndex : ceiling ≤ index := by unfold representative at small; omega
    have atEnd := checked ceiling (by unfold representative; omega)
    rw [inputAt_tail target index (by omega), inputAt_tail source index (by omega)]
    simpa [inputAt_tail target ceiling right, inputAt_tail source ceiling left] using atEnd

/-- Typed selection retains the exact first descriptor even when shapes coincide. -/
def selectTyped [DecidableEq Key] (clauses : List (TypedSignature Key Ty)) (row : Call Key Value) :=
  clauses.find? (fun clause => accepts clause.shape row)

/-- Equal shape bits preserve ordered typed descriptor selection. -/
theorem selectTyped_congr [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (left : Call Key A) (right : Call Key B)
    (same : ∀ clause ∈ clauses, accepts clause.shape left = accepts clause.shape right) :
    selectTyped clauses left = selectTyped clauses right := by
  induction clauses with
  | nil => rfl
  | cons head tail ih =>
    simp only [selectTyped, List.find?_cons]
    rw [same head (by simp)]
    split
    · rfl
    · exact ih (fun clause member => same clause (by simp [member]))

/-- Selected typed clauses belong to the original sequence, never a later fallback. -/
theorem selectTyped_member [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (row : Call Key Value) (chosen) (found : selectTyped clauses row = some chosen) : chosen ∈ clauses := by
  induction clauses with
  | nil => simp [selectTyped] at found
  | cons head tail ih =>
    by_cases hit : accepts head.shape row = true
    · have same : head = chosen := by simpa [selectTyped, List.find?_cons, hit] using found
      simp [same]
    · exact List.mem_cons_of_mem _ (ih (by simpa [selectTyped, List.find?_cons, hit] using found))

/-- Supplied argument positions must have two actual Types and a contravariant
subtype derivation; an absent default is never turned into a supplied position. -/
def inputSubtype (expected actual : Option PrototypeTypes.Ty) : Prop :=
  ∃ t s, expected = some t ∧ actual = some s ∧ PrototypeTypes.Subtype t s

/-- Finite input comparison is the existing subtype checker, not recognizer sampling. -/
def checkInput (fuel : Nat) (expected actual : Option PrototypeTypes.Ty) : Bool :=
  match expected, actual with
  | some t, some s => PrototypeTypes.check fuel t s
  | _, _ => false

/-- Every supplied input check gives the exact contravariant type relation. -/
theorem checkInput_sound (fuel : Nat) (expected actual)
    (checked : checkInput fuel expected actual = true) : inputSubtype expected actual := by
  cases expected with
  | none => simp [checkInput] at checked
  | some t =>
    cases actual with
    | none => simp [checkInput] at checked
    | some s => exact ⟨t, s, rfl, rfl, PrototypeTypes.check_sound _ _ _ checked⟩

/-- One selected cell checks exact-count covariant results and only supplied
contravariant inputs, including keyword payloads. Effects and omitted defaults
remain outside this pure judgment. -/
def cellReplaces [DecidableEq Key] (fuel : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) (row : Call Key Unit) : Bool :=
  PrototypeTypes.all₂ (PrototypeTypes.check fuel) source.outputs target.outputs &&
  (List.range row.positional.length).all (fun index => checkInput fuel (target.inputAt index) (source.inputAt index)) &&
  row.keywords.all (fun entry => checkInput fuel (RowTypes.lookup target.keywords entry.1) (RowTypes.lookup source.keywords entry.1))

/-- A checked cell carries all result and supplied argument subtype derivations. -/
theorem cellReplaces_sound [DecidableEq Key] (fuel : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) (row : Call Key Unit)
    (checked : cellReplaces fuel source target row = true) :
    PrototypeTypes.RelList PrototypeTypes.Subtype source.outputs target.outputs ∧
    (∀ index < row.positional.length, inputSubtype (target.inputAt index) (source.inputAt index)) ∧
    (∀ key ∈ row.keywords.map Prod.fst, inputSubtype (RowTypes.lookup target.keywords key) (RowTypes.lookup source.keywords key)) := by
  simp only [cellReplaces, Bool.and_eq_true] at checked
  refine ⟨PrototypeTypes.all₂_sound _ (PrototypeTypes.check_sound fuel) _ _ checked.1.1, ?_, ?_⟩
  · intro index member
    exact checkInput_sound _ _ _ ((List.all_eq_true.mp checked.1.2) index (List.mem_range.mpr member))
  · intro key member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    exact checkInput_sound _ _ _ ((List.all_eq_true.mp checked.2) entry present)

/-- The complete typed language checker compares actual first descriptors at
all finite cells. Pure coverage alone cannot authorize value-level replacement. -/
def coversTypedCalls [DecidableEq Key] (fuel : Nat) (cells : List (Call Key Unit))
    (source target : List (TypedSignature Key PrototypeTypes.Ty)) : Bool :=
  cells.all fun row => match selectTyped target row with
    | none => true
    | some expected => match selectTyped source row with
      | none => false
      | some actual => cellReplaces fuel actual expected row

/-- Full typed replacement holds for every admitted decoded call, including all
unbounded rest positions. The key universe must include that call's keys, and the
common wire interpretation is a runtime admission premise, not proved here. -/
theorem coversTypedCalls_sound [DecidableEq Key] (fuel ceiling : Nat) (keyUniverse : List Key)
    (unique : keyUniverse.Nodup) (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (bounded : ∀ signature ∈ source ++ target, (signature.inputs ++ signature.optional).length ≤ ceiling)
    (covered : coversTypedCalls fuel (callCells ceiling keyUniverse) source target = true)
    (count : Nat) (keys : List Key) (keysUnique : keys.Nodup)
    (inside : ∀ key ∈ keys, key ∈ keyUniverse) (expected)
    (selected : selectTyped target (shapeRow count keys) = some expected) :
    ∃ actual, selectTyped source (shapeRow count keys) = some actual ∧
      PrototypeTypes.RelList PrototypeTypes.Subtype actual.outputs expected.outputs ∧
      (∀ index < count, inputSubtype (expected.inputAt index) (actual.inputAt index)) ∧
      (∀ key ∈ keys, inputSubtype (RowTypes.lookup expected.keywords key) (RowTypes.lookup actual.keywords key)) := by
  let mask := keyUniverse.filter (fun key => decide (key ∈ keys))
  let cell := shapeRow (representative ceiling count) mask
  have maskUnique : mask.Nodup := unique.filter _
  have equalKeys := mask_membership keyUniverse keys inside
  have transport : ∀ clauses : List (TypedSignature Key PrototypeTypes.Ty),
      (∀ clause ∈ clauses, (clause.inputs ++ clause.optional).length ≤ ceiling) →
      selectTyped clauses cell = selectTyped clauses (shapeRow count keys) := by
    intro clauses small
    apply selectTyped_congr
    intro clause member
    calc
      accepts clause.shape cell = accepts clause.shape (shapeRow count mask) :=
        accepts_representative _ _ _ _ (by simpa [TypedSignature.shape, List.length_append] using small clause member)
      _ = accepts clause.shape (shapeRow count keys) :=
        accepts_keys _ _ _ _ maskUnique keysUnique equalKeys
  have left := transport source (fun s m => bounded s (List.mem_append_left _ m))
  have right := transport target (fun s m => bounded s (List.mem_append_right _ m))
  have targetCell : selectTyped target cell = some expected := right.trans selected
  have cellChecked := (List.all_eq_true.mp covered) cell (representative_mem ceiling count keyUniverse keys)
  simp only [targetCell] at cellChecked
  cases sourceCell : selectTyped source cell with
  | none => simp [sourceCell] at cellChecked
  | some actual =>
    have good : cellReplaces fuel actual expected cell = true := by simpa [sourceCell] using cellChecked
    obtain ⟨outputs, inputs, keywordInputs⟩ := cellReplaces_sound _ _ _ _ good
    refine ⟨actual, left.symm.trans sourceCell, outputs, ?_, ?_⟩
    · apply inputAt_representative ceiling count actual expected inputSubtype
      · exact bounded actual (List.mem_append_left _ (selectTyped_member _ _ _ sourceCell))
      · exact bounded expected (List.mem_append_right _ (selectTyped_member _ _ _ targetCell))
      · simpa [cell, shapeRow] using inputs
    · intro key present
      apply keywordInputs key
      rw [shapeRow_keys]
      exact (equalKeys key).mpr present

/-- Derive the maximum fixed prefix from every source and target clause. -/
def coverageCeiling : List (TypedSignature Key Ty) → Nat
  | [] => 0
  | head :: tail => max (head.inputs ++ head.optional).length (coverageCeiling tail)

/-- The derived ceiling bounds every clause, including shadowed ones. -/
theorem coverageCeiling_bound (clauses : List (TypedSignature Key Ty)) (clause)
    (member : clause ∈ clauses) : (clause.inputs ++ clause.optional).length ≤ coverageCeiling clauses := by
  induction clauses with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst clause; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- Standard-library stable duplicate removal supplies a duplicate-free universe.
This proves a property of `List.eraseDups`; it does not replace that operation. -/
theorem eraseDups_nodup [DecidableEq Key] (keys : List Key) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      have absent := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
      simp at absent
    · exact eraseDups_nodup (tail.filter (fun key => !key == head))
termination_by keys.length
decreasing_by
  have smaller := List.length_filter_le (fun key => !key == head) tail
  simp_wf
  omega

/-- Target-declared keys suffice: an accepted target call cannot contain another key. -/
def coverageKeys [DecidableEq Key] (target : List (TypedSignature Key Ty)) : List Key :=
  (target.flatMap (fun clause => clause.keywords.map Prod.fst)).eraseDups

/-- Typed selection commits only to an accepted shape. -/
theorem selectTyped_accepts [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (row : Call Key Value) (chosen) (found : selectTyped clauses row = some chosen) :
    accepts chosen.shape row = true := by
  induction clauses with
  | nil => simp [selectTyped] at found
  | cons head tail ih =>
    by_cases hit : accepts head.shape row = true
    · have same : head = chosen := by simpa [selectTyped, List.find?_cons, hit] using found
      simpa [same] using hit
    · exact ih (by simpa [selectTyped, List.find?_cons, hit] using found)

/-- The accepted target call supplies a duplicate-free key set in its declared universe. -/
theorem selected_keys [DecidableEq Key] (target : List (TypedSignature Key Ty))
    (count keys expected) (selected : selectTyped target (shapeRow count keys) = some expected) :
    keys.Nodup ∧ ∀ key ∈ keys, key ∈ coverageKeys target := by
  have accepted := selectTyped_accepts _ _ _ selected
  simp only [accepts, Bool.and_eq_true] at accepted
  have unique : keys.Nodup := by simpa only [shapeRow_keys] using of_decide_eq_true accepted.1.1.2
  have allowedBits : ∀ key ∈ keys, decide (key ∈ expected.keywords.map Prod.fst) = true := by
    intro key present
    exact (List.all_eq_true.mp accepted.1.2) (key, ()) (List.mem_map.mpr ⟨key, present, rfl⟩)
  have allowed : ∀ key ∈ keys, key ∈ expected.keywords.map Prod.fst :=
    fun key member => of_decide_eq_true (allowedBits key member)
  refine ⟨unique, ?_⟩
  intro key present
  simp only [coverageKeys, List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨expected, selectTyped_member _ _ _ selected, allowed key present⟩

/-- Complete finite typed replacement uses derived bounds and the target key
universe. The runtime additionally requires a shared keyword wire interpretation. -/
def replacesLanguage [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty)) : Bool :=
  coversTypedCalls fuel (callCells (coverageCeiling (source ++ target)) (coverageKeys target)) source target

/-- Every accepted decoded call of any finite or unbounded arity is safely
replaced. Results have exact-count covariance; all supplied inputs and keys have
contravariance under the original first-match descriptors. No clause fallback or
principal/host inference is assumed. -/
theorem replacesLanguage_sound [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (covered : replacesLanguage fuel source target = true) (count keys expected)
    (selected : selectTyped target (shapeRow count keys) = some expected) :
    ∃ actual, selectTyped source (shapeRow count keys) = some actual ∧
      PrototypeTypes.RelList PrototypeTypes.Subtype actual.outputs expected.outputs ∧
      (∀ index < count, inputSubtype (expected.inputAt index) (actual.inputAt index)) ∧
      (∀ key ∈ keys, inputSubtype (RowTypes.lookup expected.keywords key) (RowTypes.lookup actual.keywords key)) := by
  obtain ⟨unique, inside⟩ := selected_keys target count keys expected selected
  exact coversTypedCalls_sound fuel _ _ (eraseDups_nodup _) source target
    (fun clause member => coverageCeiling_bound _ clause member) covered count keys unique inside expected selected

end LeanPoo.Functional.FunctionSignature
