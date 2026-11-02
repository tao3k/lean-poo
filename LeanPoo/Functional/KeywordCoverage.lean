import LeanPoo.Functional.KeywordArguments

/-! Finite raw-length regions for positional sources replacing keyword targets.
Original argument order and the actual first case are retained. This advances the
article's hypothetical type protocol; host behavior and recognizer interpretation
are not established by these syntactic subtype/selection laws. -/
namespace LeanPoo.Functional.FunctionSignature

/-- Streamed in Scheme: all raw lengths between the proven decoder bounds,
clamped at the shared stationary rest representative. -/
def rawCounts (ceiling count keyCount : Nat) : List Nat :=
  (List.range (ceiling + 2)).filter (fun raw =>
    decide (min (count + 2 * keyCount) (ceiling + 1) ≤ raw ∧
      raw ≤ min (2 * count + 2 * keyCount + 1) (ceiling + 1)))

/-- Minimum, no-key, non-tail regions have no keyword/escape overhead. -/
def directRaw (ceiling count keyCount raw : Nat) : Bool :=
  decide (raw ≤ ceiling ∧ keyCount = 0 ∧ raw = count)

/-- Every supplied source position must be universal in non-direct regions.
Unused optional Types are deliberately absent from this check. -/
def rawAnyPositions (source : TypedSignature Key PrototypeTypes.Ty) (count : Nat) : Bool :=
  (List.range count).all (fun index => (source.inputAt index).any isTop)
where
  /-- Only explicit Any/top certifies protocol VALUE tokens without recognition. -/
  isTop : PrototypeTypes.Ty → Bool | .top => true | _ => false

/-- Direct cells reuse input contravariance; escaped/keyed cells use the supplied
Any witness. Both check exact-count outputs against the selected target case. -/
def rawCellReplaces [DecidableEq Key] (fuel ceiling : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) (row : Call Key Unit) (raw : Nat) : Bool :=
  if directRaw ceiling row.positional.length row.keywords.length raw then
    cellReplaces fuel source target row
  else PrototypeTypes.all₂ (PrototypeTypes.check fuel) source.outputs target.outputs &&
    rawAnyPositions source raw

/-- Actual keyword modes are part of admission. Source cases are selected by
raw arity at every region; Type/result refusal never chooses a later clause. -/
def replacesKeywordTarget [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty)) : Bool :=
  source.all (fun clause => clause.keywords.isEmpty) &&
  target.any (fun clause => !clause.keywords.isEmpty) &&
  (callCells (coverageCeiling (source ++ target)) (coverageKeys target)).all (fun row =>
    match selectTyped target row with
    | none => true
    | some expected => (rawCounts (coverageCeiling (source ++ target))
        row.positional.length row.keywords.length).all (fun raw =>
      match selectTyped source (shapeRow raw []) with
      | none => false
      | some actual => rawCellReplaces fuel (coverageCeiling (source ++ target)) actual expected row raw))

/-- Admission certifies the global mode across every source/target clause. -/
theorem replacesKeywordTarget_modes [DecidableEq Key] (fuel : Nat) (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesKeywordTarget fuel source target = true) :
    source.all (fun clause => clause.keywords.isEmpty) = true ∧
    target.any (fun clause => !clause.keywords.isEmpty) = true := by
  simp only [replacesKeywordTarget, Bool.and_eq_true] at checked
  exact checked.1

/-- Clamp both decoded and raw lengths without losing any feasible spelling.
The rest representative is strictly beyond every fixed/optional source prefix. -/
theorem rawCounts_complete (ceiling count keyCount raw : Nat)
    (lower : count + 2 * keyCount ≤ raw)
    (upper : raw ≤ 2 * count + 2 * keyCount + 1) :
    representative ceiling raw ∈ rawCounts ceiling (representative ceiling count) keyCount := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (by unfold representative; omega), ?_⟩
  apply decide_eq_true
  unfold representative
  omega

/-- The key-mask enumeration preserves cardinality as well as membership. -/
theorem coverageMask_length [DecidableEq Key] (target : List (TypedSignature Key Ty))
    (keys : List Key) (unique : keys.Nodup) (inside : ∀ key ∈ keys, key ∈ coverageKeys target) :
    ((coverageKeys target).filter (fun key => decide (key ∈ keys))).length = keys.length := by
  have same := mask_membership (coverageKeys target) keys inside
  apply Nat.le_antisymm
  · exact List.Nodup.length_le_of_subset ((eraseDups_nodup _).filter _) (fun key member => (same key).mp member)
  · exact List.Nodup.length_le_of_subset unique (fun key member => (same key).mpr member)

/-- Any witnesses give explicit top Types at all provided positions. -/
theorem rawAnyPositions_sound (source : TypedSignature Key PrototypeTypes.Ty) (count : Nat)
    (checked : rawAnyPositions source count = true) :
    ∀ index < count, source.inputAt index = some .top := by
  intro index member
  have bit := List.all_eq_true.mp checked index (List.mem_range.mpr member)
  cases found : source.inputAt index with
  | none => simp [found] at bit
  | some ty => cases ty <;> simp_all [rawAnyPositions.isTop]

/-- A selected raw cell retains exact output variance and either direct input
variance or universal supplied source Types, never a later-case repair. -/
theorem rawCellReplaces_sound [DecidableEq Key] (fuel ceiling : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) (row : Call Key Unit) (raw : Nat)
    (checked : rawCellReplaces fuel ceiling source target row raw = true) :
    PrototypeTypes.RelList PrototypeTypes.Subtype source.outputs target.outputs ∧
    ((directRaw ceiling row.positional.length row.keywords.length raw = true ∧
       ∀ index < row.positional.length, inputSubtype (target.inputAt index) (source.inputAt index)) ∨
     (directRaw ceiling row.positional.length row.keywords.length raw = false ∧
       ∀ index < raw, source.inputAt index = some .top)) := by
  unfold rawCellReplaces at checked
  split at checked
  · obtain ⟨outputs, inputs, _⟩ := cellReplaces_sound fuel source target row checked
    exact ⟨outputs, Or.inl ⟨by assumption, inputs⟩⟩
  · simp only [Bool.and_eq_true] at checked
    exact ⟨PrototypeTypes.all₂_sound _ (PrototypeTypes.check_sound fuel) _ _ checked.1,
      Or.inr ⟨by simp_all, rawAnyPositions_sound source raw checked.2⟩⟩

/-- Every actual first source case has an admitted cell witness at the canonical
raw/target representatives. Bounds and key masks are derived from the descriptors. -/
theorem replacesKeywordTarget_cell [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesKeywordTarget fuel source target = true)
    (count : Nat) (keys : List Key) (expected)
    (selected : selectTyped target (shapeRow count keys) = some expected)
    (raw : Nat) (lower : count + 2 * keys.length ≤ raw)
    (upper : raw ≤ 2 * count + 2 * keys.length + 1) :
    let ceiling := coverageCeiling (source ++ target)
    let mask := (coverageKeys target).filter (fun key => decide (key ∈ keys))
    ∃ actual, selectTyped source (shapeRow (representative ceiling raw) []) = some actual ∧
      rawCellReplaces fuel ceiling actual expected (shapeRow (representative ceiling count) mask)
        (representative ceiling raw) = true := by
  let ceiling := coverageCeiling (source ++ target)
  let mask := (coverageKeys target).filter (fun key => decide (key ∈ keys))
  obtain ⟨unique, inside⟩ := selected_keys target count keys expected selected
  have maskLength := coverageMask_length target keys unique inside
  have found := (selectTyped_cell target ceiling count keys
    (fun clause member => coverageCeiling_bound _ clause (List.mem_append_right _ member)) unique inside).trans selected
  simp only [replacesKeywordTarget, Bool.and_eq_true] at checked
  have valid := List.all_eq_true.mp checked.2 _ (representative_mem ceiling count (coverageKeys target) keys)
  change (match selectTyped target (shapeRow (representative ceiling count) mask) with
    | none => true
    | some clause => (rawCounts ceiling (shapeRow (representative ceiling count) mask).positional.length
      (shapeRow (representative ceiling count) mask).keywords.length).all (fun rawCount =>
      match selectTyped source (shapeRow rawCount []) with
      | none => false
      | some actual => rawCellReplaces fuel ceiling actual clause
          (shapeRow (representative ceiling count) mask) rawCount)) = true at valid
  rw [found] at valid
  have maskLength' : mask.length = keys.length := maskLength
  simp only [shapeRow, List.length_replicate, List.length_map, maskLength'] at valid
  have rawValid := List.all_eq_true.mp valid _ (rawCounts_complete ceiling count keys.length raw lower upper)
  change (match selectTyped source (shapeRow (representative ceiling raw) []) with
    | none => false
    | some actual => rawCellReplaces fuel ceiling actual expected
        (shapeRow (representative ceiling count) mask) (representative ceiling raw)) = true at rawValid
  cases sourceCell : selectTyped source (shapeRow (representative ceiling raw) []) with
  | none => rw [sourceCell] at rawValid; contradiction
  | some actual => exact ⟨actual, sourceCell, by simpa only [sourceCell] using rawValid⟩

/-- A representative that is direct cannot denote a longer tail row. -/
theorem directRaw_lift (ceiling count keyCount raw : Nat)
    (lower : count + 2 * keyCount ≤ raw)
    (direct : directRaw ceiling (representative ceiling count) keyCount (representative ceiling raw) = true) :
    keyCount = 0 ∧ raw = count ∧ count ≤ ceiling := by
  have bits : representative ceiling raw ≤ ceiling ∧ keyCount = 0 ∧
      representative ceiling raw = representative ceiling count := of_decide_eq_true direct
  unfold representative at bits
  omega

/-- Every successfully decoded target call is covered by its ACTUAL first source
case. Direct rows retain exact input variance; all other rows admit every supplied
raw token as Any. This quantifies over unbounded rest rows and every escape/key
order. It does not prove host arity, defaults, effects or recognizer interpretation. -/
theorem replacesKeywordTarget_sound [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesKeywordTarget fuel source target = true)
    (tokens : List (ArgumentToken Key Value)) (row)
    (decoded : decodeKeyword tokens = some row) (expected)
    (selected : selectTyped target (shapeRow row.positional.length (row.keywords.map Prod.fst)) = some expected) :
    ∃ actual, selectTyped source (Call.mk tokens ([] : List (Key × ArgumentToken Key Value))) = some actual ∧
      PrototypeTypes.RelList PrototypeTypes.Subtype actual.outputs expected.outputs ∧
      ((row.keywords = [] ∧ row.positional = tokens ∧
        ∀ index < tokens.length, inputSubtype (expected.inputAt index) (actual.inputAt index)) ∨
       (∀ index < tokens.length, actual.inputAt index = some .top)) := by
  let ceiling := coverageCeiling (source ++ target)
  let keys := row.keywords.map Prod.fst
  let mask := (coverageKeys target).filter (fun key => decide (key ∈ keys))
  have lower := decode_minimum tokens row decoded
  have upper := decode_maximum tokens row decoded
  obtain ⟨actual, found, good⟩ := replacesKeywordTarget_cell fuel source target checked
    row.positional.length keys expected selected tokens.length
    (by simpa [keys] using lower) (by simpa [keys] using upper)
  have sourceCount : selectTyped source (shapeRow (representative ceiling tokens.length) []) =
      selectTyped source (shapeRow tokens.length []) := by
    apply selectTyped_congr
    intro clause member
    exact accepts_representative _ _ _ _
      (by simpa [TypedSignature.shape] using
        coverageCeiling_bound (source ++ target) clause (List.mem_append_left _ member))
  have erasure : selectTyped source (shapeRow tokens.length []) =
      selectTyped source (Call.mk tokens ([] : List (Key × ArgumentToken Key Value))) :=
    selectTyped_congr source _ _ (fun clause _ => accepts_shapeRow clause.shape (Call.mk tokens []))
  obtain ⟨outputs, inputs⟩ := rawCellReplaces_sound fuel ceiling actual expected
    (shapeRow (representative ceiling row.positional.length) mask) (representative ceiling tokens.length) good
  refine ⟨actual, erasure.symm.trans (sourceCount.symm.trans found), outputs, ?_⟩
  rcases inputs with ⟨direct, ordinary⟩ | ⟨_, universal⟩
  · obtain ⟨unique, inside⟩ := selected_keys target row.positional.length keys expected selected
    have maskLength : mask.length = keys.length := coverageMask_length target keys unique inside
    have direct' : directRaw ceiling (representative ceiling row.positional.length) keys.length
        (representative ceiling tokens.length) = true := by
      simpa only [shapeRow, List.length_replicate, List.length_map, maskLength] using direct
    obtain ⟨empty, equal, bounded⟩ := directRaw_lift ceiling row.positional.length keys.length tokens.length
      (by simpa [keys] using lower) direct'
    have noKeys : row.keywords = [] := by simpa [keys] using empty
    have noEscapes := decode_direct tokens row decoded noKeys equal.symm
    refine Or.inl ⟨noKeys, noEscapes, ?_⟩
    intro index member
    apply ordinary index
    simp only [shapeRow, List.length_replicate]
    simpa [representative, Nat.min_eq_left (by omega : row.positional.length ≤ ceiling + 1), equal] using member
  · apply Or.inr
    have width := coverageCeiling_bound (source ++ target) actual
      (List.mem_append_left _ (selectTyped_member _ _ _ found))
    apply inputAt_representative ceiling tokens.length actual actual
      (fun _ actual => actual = some .top) width width
    simpa only [shapeRow, List.length_replicate] using universal

end LeanPoo.Functional.FunctionSignature
