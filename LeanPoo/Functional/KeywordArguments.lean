import LeanPoo.Functional.FunctionCoverage

/-! Controlled cross-mode Function replacement. This is future type-protocol
work, not a claim that the original Racket implementation has a static type
system. Tokens model the existing Gerbil decoder; arbitrary recognizers and
host procedure arity/totality remain separate runtime obligations. -/
namespace LeanPoo.Functional.FunctionSignature

/-- Outer protocol tokens are distinct from ordinary values. A container whose
payload contains a keyword still has an ordinary outer carrier. -/
inductive ArgumentToken (Key Value : Type) where
  | value : Value → ArgumentToken Key Value
  | keyword : Key → ArgumentToken Key Value
  | keyEscape : ArgumentToken Key Value
  | restEscape : ArgumentToken Key Value
  deriving Repr, DecidableEq

/-- Decode the existing keyword language, retaining supplied values and order.
Escaped values are positional; rest escape ends interpretation; duplicate and
dangling keys refuse before any recognizer or body can run. -/
def decodeKeyword [DecidableEq Key] : List (ArgumentToken Key Value) → Option (Call Key (ArgumentToken Key Value))
  | [] => some ⟨[], []⟩
  | .restEscape :: tail => some ⟨tail, []⟩
  | .keyEscape :: [] => none
  | .keyword _ :: [] => none
  | .keyEscape :: value :: tail => do
      let row ← decodeKeyword tail
      return { row with positional := value :: row.positional }
  | .keyword key :: value :: tail => do
      let row ← decodeKeyword tail
      if key ∈ row.keywords.map Prod.fst then none
      else return { row with keywords := (key, value) :: row.keywords }
  | .value value :: tail => do
      let row ← decodeKeyword tail
      return { row with positional := .value value :: row.positional }

/-- Plain mode keeps the entire original row, including protocol-looking data. -/
def decodeArguments [DecidableEq Key] (tokens : List (ArgumentToken Key Value)) (mode : Bool) :=
  if mode then decodeKeyword tokens else some (Call.mk tokens [])

/-- Ordinary outer carriers decode identically in both modes. No reencoding,
default computation, or payload traversal is involved in this equality. -/
theorem decode_ordinary [DecidableEq Key] (values : List Value) :
    decodeKeyword (values.map (ArgumentToken.value (Key := Key))) =
      some ⟨values.map ArgumentToken.value, []⟩ := by
  induction values with
  | nil => rfl
  | cons value tail ih => simp [decodeKeyword, ih]

/-- Every successful keyword row requires at least one raw token per position
and two per supplied key. Escapes can increase this cost, never decrease it. -/
theorem decode_minimum [DecidableEq Key] (tokens : List (ArgumentToken Key Value))
    (row : Call Key (ArgumentToken Key Value)) (decoded : decodeKeyword tokens = some row) :
    row.positional.length + 2 * row.keywords.length ≤ tokens.length := by
  cases tokens with
  | nil => simp [decodeKeyword] at decoded; subst row; simp
  | cons head tail =>
    cases head with
    | restEscape => simp [decodeKeyword] at decoded; subst row; simp
    | value value =>
      cases found : decodeKeyword tail with
      | none => simp [decodeKeyword, found] at decoded
      | some rest =>
        simp [decodeKeyword, found] at decoded; subst row
        have bound := decode_minimum tail rest found
        simp only [List.length_cons]; omega
    | keyEscape =>
      cases tail with
      | nil => simp [decodeKeyword] at decoded
      | cons value rest =>
        cases found : decodeKeyword rest with
        | none => simp [decodeKeyword, found] at decoded
        | some next =>
          simp [decodeKeyword, found] at decoded; subst row
          have bound := decode_minimum rest next found
          simp only [List.length_cons]; omega
    | keyword key =>
      cases tail with
      | nil => simp [decodeKeyword] at decoded
      | cons value rest =>
        cases found : decodeKeyword rest with
        | none => simp [decodeKeyword, found] at decoded
        | some next =>
          by_cases duplicate : key ∈ next.keywords.map Prod.fst
          · simp [decodeKeyword, found, duplicate] at decoded
          · simp [decodeKeyword, found, duplicate] at decoded; subst row
            have bound := decode_minimum rest next found
            simp only [List.length_cons]; omega

termination_by tokens.length

/-- A source transport admits every raw token at each fixed/optional position
and through an unbounded rest tail. The first clause is mandatory: target decoded
arity must never select a more favorable later plain clause. -/
def rawTransport (source : TypedSignature Key PrototypeTypes.Ty) : Bool :=
  source.inputs.all isTop && source.optional.all isTop &&
  (match source.rest with | some .top => true | _ => false) &&
  source.keywords.isEmpty && source.requiredKeywords.isEmpty
where
  /-- This decidable syntactic witness makes no user recognizer calls. -/
  isTop : PrototypeTypes.Ty → Bool | .top => true | _ => false

/-- Every supplied raw position receives Any, including optional and arbitrarily
long rest positions. Protocol tokens therefore need no fabricated Type syntax. -/
theorem rawTransport_inputAt (source : TypedSignature Key PrototypeTypes.Ty)
    (checked : rawTransport source = true) (index : Nat) : source.inputAt index = some .top := by
  simp only [rawTransport, Bool.and_eq_true] at checked
  have tailTop : source.rest = some .top := by
    cases h : source.rest with
    | none => simp [h] at checked
    | some term => cases term <;> simp_all
  have fixedTop : ∀ ty ∈ source.inputs ++ source.optional, ty = PrototypeTypes.Ty.top := by
    intro ty member
    have bit : rawTransport.isTop ty = true := by
      rcases List.mem_append.mp member with left | right
      · exact List.all_eq_true.mp checked.1.1.1.1 ty left
      · exact List.all_eq_true.mp checked.1.1.1.2 ty right
    cases ty <;> simp_all [rawTransport.isTop]
  cases found : (source.inputs ++ source.optional)[index]? with
  | none => simp [TypedSignature.inputAt, found, tailTop]
  | some ty => simp [TypedSignature.inputAt, found, fixedTop ty (List.mem_of_getElem? found)]

/-- A transport's first clause accepts the unchanged raw row above its minimum. -/
theorem rawTransport_accepts [DecidableEq Key] (source : TypedSignature Key PrototypeTypes.Ty)
    (checked : rawTransport source = true) (tokens : List (ArgumentToken Key Value))
    (enough : source.inputs.length ≤ tokens.length) :
    accepts source.shape (Call.mk tokens []) = true := by
  simp only [rawTransport, Bool.and_eq_true] at checked
  have rest : source.rest.isSome = true := by
    cases h : source.rest with
    | none => simp [h] at checked
    | some term => cases term <;> simp_all
  have noRequired : source.requiredKeywords = [] := List.isEmpty_iff.mp checked.2
  simp [accepts, TypedSignature.shape, enough, rest, noRequired]

/-- A finite cell checks the true minimum raw length and exact-count covariant
results. Keyword/escape VALUES never enter the Type-expression comparator. -/
def rawCellReplaces (fuel : Nat) (source target : TypedSignature Key PrototypeTypes.Ty)
    (row : Call Key Unit) : Bool :=
  decide (source.inputs.length ≤ row.positional.length + 2 * row.keywords.length) &&
  PrototypeTypes.all₂ (PrototypeTypes.check fuel) source.outputs target.outputs

/-- Target cells are reused unchanged. The plain source always contributes its
first descriptor; the witness is sufficient, not maximal raw-language inclusion. -/
def replacesKeywordTarget [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty)) : Bool :=
  match source with
  | [] => false
  | first :: _ => rawTransport first &&
    (callCells (coverageCeiling (source ++ target)) (coverageKeys target)).all (fun row =>
      match selectTyped target row with
      | none => true
      | some expected => rawCellReplaces fuel first expected row)

/-- Canonical target cells preserve the actual first selected clause. -/
theorem selectTyped_cell [DecidableEq Key] (target : List (TypedSignature Key Ty))
    (ceiling count : Nat) (keys : List Key)
    (bounded : ∀ clause ∈ target, (clause.inputs ++ clause.optional).length ≤ ceiling)
    (unique : keys.Nodup) (inside : ∀ key ∈ keys, key ∈ coverageKeys target) :
    selectTyped target (shapeRow (representative ceiling count)
      ((coverageKeys target).filter (fun key => decide (key ∈ keys)))) =
    selectTyped target (shapeRow count keys) := by
  apply selectTyped_congr
  intro clause member
  rw [accepts_representative _ _ _ _ (by simpa [TypedSignature.shape] using bounded clause member)]
  exact accepts_keys _ _ _ _ ((eraseDups_nodup _).filter _) unique (mask_membership _ _ inside)

/-- Finite raw-transport checking covers every successfully decoded target row,
all keyword orders and escape spellings, and arbitrarily long rest tails. -/
theorem replacesKeywordTarget_sound [DecidableEq Key] (fuel : Nat)
    (first : TypedSignature Key PrototypeTypes.Ty) (later target)
    (checked : replacesKeywordTarget fuel (first :: later) target = true)
    (tokens : List (ArgumentToken Key Value)) (row)
    (decoded : decodeKeyword tokens = some row) (expected)
    (selected : selectTyped target (shapeRow row.positional.length (row.keywords.map Prod.fst)) = some expected) :
    selectTyped (first :: later) (Call.mk tokens ([] : List (Key × ArgumentToken Key Value))) = some first ∧
    PrototypeTypes.RelList PrototypeTypes.Subtype first.outputs expected.outputs := by
  simp only [replacesKeywordTarget, Bool.and_eq_true] at checked
  let ceiling := coverageCeiling ((first :: later) ++ target)
  let keys := row.keywords.map Prod.fst
  obtain ⟨unique, inside⟩ := selected_keys _ _ _ _ selected
  let mask := (coverageKeys target).filter (fun key => decide (key ∈ keys))
  let cell := shapeRow (representative ceiling row.positional.length) mask
  have found : selectTyped target cell = some expected :=
    (selectTyped_cell target ceiling _ keys
      (fun clause member => coverageCeiling_bound _ _ (List.mem_append_right _ member)) unique inside).trans selected
  have valid := (List.all_eq_true.mp checked.2) cell (representative_mem ceiling _ _ keys)
  simp only [found, rawCellReplaces, Bool.and_eq_true] at valid
  have small : first.inputs.length ≤ cell.positional.length + 2 * cell.keywords.length := of_decide_eq_true valid.1
  have maskLength : mask.length ≤ keys.length :=
    List.Nodup.length_le_of_subset ((eraseDups_nodup _).filter _)
      (fun _ member => (mask_membership _ _ inside _).mp member)
  have minimum := decode_minimum tokens row decoded
  have enough : first.inputs.length ≤ tokens.length := by
    simp only [cell, shapeRow, List.length_replicate, List.length_map] at small
    have rep : representative ceiling row.positional.length ≤ row.positional.length := Nat.min_le_left _ _
    simp only [keys, List.length_map] at maskLength
    omega
  refine ⟨?_, PrototypeTypes.all₂_sound _ (PrototypeTypes.check_sound fuel) _ _ valid.2⟩
  simp [selectTyped, rawTransport_accepts first checked.1 tokens enough]

/-- Ground finite Types with a stable ordinary outer carrier. Union exposes its
alternatives; top admits protocol tokens. Fuel exhaustion is conservative false. -/
def keywordStable : Nat → PrototypeTypes.Ty → Bool
  | 0, _ => false
  | fuel + 1, .union branches => branches.all (keywordStable fuel)
  | _ + 1, .top => false
  | _ + 1, _ => true

/-- Stability applies only to actually supplied positions of the selected target. -/
def stablePositions (fuel : Nat) (target : TypedSignature Key PrototypeTypes.Ty)
    (count : Nat) : Bool :=
  (List.range count).all (fun index => (target.inputAt index).any (keywordStable fuel))

/-- Reuse the complete typed coverage checker, adding a finite stability witness
for positional target calls. Absent defaults and shadowed clauses are not checked. -/
def replacesPositionalTarget [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty)) : Bool :=
  replacesLanguage fuel source target &&
  (callCells (coverageCeiling (source ++ target)) []).all (fun row =>
    match selectTyped target row with
    | none => true
    | some expected => stablePositions fuel expected row.positional.length)

/-- Positional target stability is universal in supplied arity, including rest
positions. This extends the same finite representative used for typed variance. -/
theorem replacesPositionalTarget_stable [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesPositionalTarget fuel source target = true) (count expected)
    (selected : selectTyped target (shapeRow count []) = some expected) :
    ∀ index < count, (expected.inputAt index).any (keywordStable fuel) = true := by
  simp only [replacesPositionalTarget, Bool.and_eq_true] at checked
  let ceiling := coverageCeiling (source ++ target)
  have transport : selectTyped target (shapeRow (representative ceiling count) []) =
      selectTyped target (shapeRow count []) := by
    apply selectTyped_congr
    intro clause member
    exact accepts_representative _ _ _ _
      (by simpa [TypedSignature.shape] using
        coverageCeiling_bound (source ++ target) clause (List.mem_append_right _ member))
  have present : shapeRow (representative ceiling count) ([] : List Key) ∈ callCells ceiling [] := by
    simpa using representative_mem ceiling count ([] : List Key) []
  have valid := (List.all_eq_true.mp checked.2) _ present
  change (match selectTyped target (shapeRow (representative ceiling count) []) with
    | none => true
    | some clause => stablePositions fuel clause (shapeRow (representative ceiling count) ([] : List Key)).positional.length) = true at valid
  rw [transport, selected] at valid
  simp only [stablePositions, shapeRow, List.length_replicate] at valid
  have small := fun index member => (List.all_eq_true.mp valid) index (List.mem_range.mpr member)
  have width := coverageCeiling_bound (source ++ target) expected
    (List.mem_append_right _ (selectTyped_member _ _ _ selected))
  have lifted := inputAt_representative ceiling count expected expected
    (fun expected _ => expected.any (keywordStable fuel) = true) width width small
  exact lifted

/-- A runtime interpretation premise ties stable ground Types to ordinary outer
carriers. Arbitrary custom/effectful recognizers are intentionally not axiomatized. -/
theorem stable_row_ordinary [DecidableEq Key] (fuel : Nat)
    (target : TypedSignature Key PrototypeTypes.Ty) (tokens : List (ArgumentToken Key Value))
    (recognizes : PrototypeTypes.Ty → ArgumentToken Key Value → Prop)
    (carrier : ∀ ty token, keywordStable fuel ty = true → recognizes ty token →
      ∃ value, token = .value value)
    (stable : ∀ index < tokens.length, (target.inputAt index).any (keywordStable fuel) = true)
    (typed : ∀ index (inside : index < tokens.length), ∃ ty,
      target.inputAt index = some ty ∧ recognizes ty tokens[index]) :
    ∃ values : List Value, tokens = values.map ArgumentToken.value := by
  have ordinary : ∀ token ∈ tokens, ∃ value, token = ArgumentToken.value value := by
    intro token member
    obtain ⟨index, inside, equal⟩ := List.mem_iff_getElem.mp member
    obtain ⟨ty, formal, recognized⟩ := typed index inside
    have good : keywordStable fuel ty = true := by simpa [formal] using stable index inside
    simpa [equal] using carrier ty tokens[index] good recognized
  clear stable typed target carrier recognizes
  induction tokens with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
    obtain ⟨value, rfl⟩ := ordinary head (by simp)
    obtain ⟨values, rfl⟩ := ih (fun token member => ordinary token (by simp [member]))
    exact ⟨value :: values, rfl⟩

/-- Under the explicit runtime carrier premise, positional target values cannot
change interpretation in keyword mode. Selection and variance use the existing
coverage theorem; no wrapper translates the caller's original raw row. -/
theorem replacesPositionalTarget_decodes [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesPositionalTarget fuel source target = true)
    (tokens : List (ArgumentToken Key Value)) (expected)
    (selected : selectTyped target (shapeRow tokens.length []) = some expected)
    (recognizes : PrototypeTypes.Ty → ArgumentToken Key Value → Prop)
    (carrier : ∀ ty token, keywordStable fuel ty = true → recognizes ty token → ∃ value, token = .value value)
    (typed : ∀ index (inside : index < tokens.length), ∃ ty,
      expected.inputAt index = some ty ∧ recognizes ty tokens[index]) :
    decodeArguments tokens true = decodeArguments tokens false := by
  obtain ⟨values, rfl⟩ := stable_row_ordinary fuel expected tokens recognizes carrier
    (replacesPositionalTarget_stable fuel source target checked _ _ selected) typed
  simp [decodeArguments, decode_ordinary]

/-- Successful positional replacement gives both raw decoding agreement and all
first-clause variance obligations under the explicit carrier interpretation. -/
theorem replacesPositionalTarget_sound [DecidableEq Key] (fuel : Nat)
    (source target : List (TypedSignature Key PrototypeTypes.Ty))
    (checked : replacesPositionalTarget fuel source target = true)
    (tokens : List (ArgumentToken Key Value)) (expected)
    (selected : selectTyped target (shapeRow tokens.length []) = some expected)
    (recognizes : PrototypeTypes.Ty → ArgumentToken Key Value → Prop)
    (carrier : ∀ ty token, keywordStable fuel ty = true → recognizes ty token → ∃ value, token = .value value)
    (typed : ∀ index (inside : index < tokens.length), ∃ ty,
      expected.inputAt index = some ty ∧ recognizes ty tokens[index]) :
    decodeArguments tokens true = decodeArguments tokens false ∧
    ∃ actual, selectTyped source (shapeRow tokens.length []) = some actual ∧
      PrototypeTypes.RelList PrototypeTypes.Subtype actual.outputs expected.outputs ∧
      (∀ index < tokens.length, inputSubtype (expected.inputAt index) (actual.inputAt index)) := by
  refine ⟨replacesPositionalTarget_decodes fuel source target checked tokens expected selected recognizes carrier typed, ?_⟩
  have parts := checked
  simp only [replacesPositionalTarget, Bool.and_eq_true] at parts
  have ordinary := parts.1
  obtain ⟨actual, found, outputs, inputs, _⟩ := replacesLanguage_sound fuel source target ordinary _ [] expected selected
  exact ⟨actual, found, outputs, inputs⟩

end LeanPoo.Functional.FunctionSignature
