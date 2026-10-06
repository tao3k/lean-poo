import LeanPoo.Prototype.RecordDispatch
import LeanPoo.Prototype.FiniteFix

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperRecordDispatch

abbrev Value : String → Type := fun _ => Int
abbrev Source := CheckedRecord String Value (String × String)

private def missing (key : String) : String × String := ("unbound slot", key)

/-! The paper's x=1, y=2 function record, with its queried-key error. -/
private def sourceBase : Source := fun key =>
  if key = "x" then .ok 1
  else if key = "y" then .ok 2
  else .error (missing key)

private theorem sourceBase_canonical :
    ∀ key error, sourceBase key = .error error → error = missing key := by
  intro key error h
  by_cases hx : key = "x"
  · simp [sourceBase, hx] at h
  · by_cases hy : key = "y"
    · simp [sourceBase, hy] at h
    · simpa [sourceBase, hx, hy] using h.symm

private def targetBase : Record String Value := sourceBase.toRecord

private theorem base_exact : targetBase.toChecked missing = sourceBase :=
  CheckedRecord.toChecked_toRecord sourceBase missing sourceBase_canonical

private def sourceSet : Proto Source Source Source :=
  fun _ inherited => CheckedRecord.slot "x" 3 inherited

private def sourceDouble : Proto Source Source Source :=
  fun _ inherited => CheckedRecord.modify "x" (· * 2) inherited

private def targetSet : Proto (Record String Value) (Record String Value)
    (Record String Value) := Record.slot "x" 3

private def targetDouble : Proto (Record String Value) (Record String Value)
    (Record String Value) := Record.modify "x" (· * 2)

/-- The paper's mixed override and inherited read agree on every String key,
including the exact missing-slot error for all other keys. -/
private theorem mixed_exact (sourceSelf : Source) (targetSelf : Record String Value) :
    ((compose targetDouble targetSet) targetSelf targetBase).toChecked missing =
      (compose sourceDouble sourceSet) sourceSelf sourceBase := by
  simp only [compose, targetDouble, targetSet, sourceDouble, sourceSet,
    Record.toChecked_modify, Record.toChecked_slot, base_exact]

private def sourceSumCalculate (self : Source) : Int :=
  (self "x").toOption.getD 0 + (self "y").toOption.getD 0

private def targetSumCalculate (self : Record String Value) : Int :=
  (self.lookup "x").getD 0 + (self.lookup "y").getD 0

private theorem calculate_exact (sourceSelf : Source)
    (targetSelf : Record String Value)
    (related : targetSelf.toChecked missing = sourceSelf) :
    targetSumCalculate targetSelf = sourceSumCalculate sourceSelf := by
  cases related
  simp [sourceSumCalculate, targetSumCalculate, Record.toChecked_toOption]

private def sourceSum : Proto Source Source Source :=
  fun self inherited => CheckedRecord.compute "sum" sourceSumCalculate self inherited

private def targetSum : Proto (Record String Value) (Record String Value)
    (Record String Value) := Record.compute "sum" targetSumCalculate

private def sourceLayers : Proto Source Source Source :=
  compose sourceSum (compose sourceDouble sourceSet)

private def targetLayers : Proto (Record String Value) (Record String Value)
    (Record String Value) :=
  compose targetSum (compose targetDouble targetSet)

private theorem layer_exact (sourceSelf : Source) (targetSelf : Record String Value)
    (related : targetSelf.toChecked missing = sourceSelf) :
    (targetLayers targetSelf targetBase).toChecked missing =
      sourceLayers sourceSelf sourceBase := by
  exact Record.toChecked_compute "sum" targetSumCalculate sourceSumCalculate
    targetSelf ((compose targetDouble targetSet) targetSelf targetBase)
    sourceSelf ((compose sourceDouble sourceSet) sourceSelf sourceBase) missing
    (calculate_exact sourceSelf targetSelf related) (mixed_exact sourceSelf targetSelf)

/-- The paper's checked function record and the typed record agree on every
String key after any number of recursive prototype unfoldings. -/
private theorem every_depth_exact (depth : Nat) :
    (FiniteFix.iterate targetLayers targetBase targetBase depth).toChecked missing =
      FiniteFix.iterate sourceLayers sourceBase sourceBase depth := by
  exact FiniteFix.iterate_relation sourceLayers targetLayers
    (fun source target => target.toChecked missing = source)
    sourceBase targetBase sourceBase targetBase base_exact
    (fun source target related => layer_exact source target related) depth

/-! The paper's final-self calculation propagates errors from x and y. The
total helper above is used only where both reads succeed; the next lemmas
establish that this premise holds at every reachable unfolding depth. -/
private def sourcePaperSum (self : Source) : Except (String × String) Int := do
  return (← self "x") + (← self "y")

private def sourcePaperSumLayer : Proto Source Source Source :=
  fun self inherited query =>
    if query = "sum" then sourcePaperSum self else inherited query

private def sourcePaperLayers : Proto Source Source Source :=
  compose sourcePaperSumLayer (compose sourceDouble sourceSet)

private theorem source_x_valid (depth : Nat) :
    ∃ x, (FiniteFix.iterate sourceLayers sourceBase sourceBase depth) "x" = .ok x := by
  cases depth with
  | zero => exact ⟨1, rfl⟩
  | succ _ => exact ⟨6, rfl⟩

private theorem source_y_valid (depth : Nat) :
    (FiniteFix.iterate sourceLayers sourceBase sourceBase depth) "y" = .ok 2 := by
  cases depth <;> rfl

private theorem paper_sum_exact (self : Source) (x : Int)
    (hx : self "x" = .ok x) (hy : self "y" = .ok 2) :
    sourcePaperSum self = .ok (sourceSumCalculate self) := by
  simp [sourcePaperSum, sourceSumCalculate, hx, hy] <;> rfl

private theorem paper_layer_exact (self : Source) (x : Int)
    (hx : self "x" = .ok x) (hy : self "y" = .ok 2) :
    sourcePaperLayers self sourceBase = sourceLayers self sourceBase := by
  funext query
  by_cases hsum : query = "sum"
  · subst query
    simp [sourcePaperLayers, sourcePaperSumLayer, sourceLayers, sourceSum,
      CheckedRecord.compute, CheckedRecord.slot, compose,
      paper_sum_exact self x hx hy]
  · simp [sourcePaperLayers, sourcePaperSumLayer, sourceLayers, sourceSum,
      CheckedRecord.compute, CheckedRecord.slot, compose, hsum]

private theorem paper_finite_exact (depth : Nat) :
    FiniteFix.iterate sourcePaperLayers sourceBase sourceBase depth =
      FiniteFix.iterate sourceLayers sourceBase sourceBase depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [FiniteFix.unfold, FiniteFix.unfold, ih]
    obtain ⟨x, hx⟩ := source_x_valid depth
    exact paper_layer_exact _ x hx (source_y_valid depth)

/-- The executable paper-style error propagation and typed Option carrier
have identical checked observations at every finite unfolding depth. -/
private theorem paper_record_correspondence (depth : Nat) :
    (FiniteFix.iterate targetLayers targetBase targetBase depth).toChecked missing =
      FiniteFix.iterate sourcePaperLayers sourceBase sourceBase depth := by
  rw [paper_finite_exact]
  exact every_depth_exact depth

private theorem source_paper_stable :
    FiniteFix.iterate sourcePaperLayers sourceBase sourceBase 2 =
      FiniteFix.iterate sourcePaperLayers sourceBase sourceBase 3 := by
  funext key
  by_cases hsum : key = "sum"
  · subst key
    rfl
  · simp [FiniteFix.iterate, sourcePaperLayers, sourcePaperSumLayer,
      sourceDouble, sourceSet, compose, CheckedRecord.slot,
      CheckedRecord.modify, hsum]

private def sourcePaperFixed : { value : Source //
    sourcePaperLayers value sourceBase = value } :=
  FiniteFix.certified sourcePaperLayers sourceBase sourceBase 2 source_paper_stable

private theorem target_observation_stable (extra : Nat) :
    (FiniteFix.iterate targetLayers targetBase targetBase (2 + extra)).toChecked missing =
      (FiniteFix.iterate targetLayers targetBase targetBase 2).toChecked missing := by
  rw [paper_record_correspondence, paper_record_correspondence]
  exact FiniteFix.stable_forever sourcePaperLayers sourceBase sourceBase
    2 source_paper_stable extra

private theorem x_observation (sourceSelf : Source) :
    ((compose sourceDouble sourceSet) sourceSelf sourceBase) "x" = .ok 6 := rfl

private theorem y_observation (sourceSelf : Source) :
    ((compose sourceDouble sourceSet) sourceSelf sourceBase) "y" = .ok 2 := rfl

private theorem unbound_observation (sourceSelf : Source) :
    ((compose sourceDouble sourceSet) sourceSelf sourceBase) "z" =
      .error (missing "z") := rfl

private def observed :=
  ((compose targetDouble targetSet) targetBase targetBase).toChecked missing

#guard (match observed "x" with | .ok value => value == 6 | .error _ => false)
#guard (match observed "y" with | .ok value => value == 2 | .error _ => false)
#guard (match observed "z" with
  | .ok _ => false
  | .error (label, key) => label == "unbound slot" && key == "z")

private def observedFixed :=
  (FiniteFix.iterate targetLayers targetBase targetBase 2).toChecked missing

#guard (match observedFixed "sum" with | .ok value => value == 8 | .error _ => false)
#guard (match observedFixed "z" with
  | .ok _ => false
  | .error (label, key) => label == "unbound slot" && key == "z")

#eval IO.println "POOF-RECORD-RELATION-OK allStringKeys=true allFiniteDepths=true sourceFixedDepth=2 checkedErrors=true"

#print axioms CheckedRecord.toChecked_toRecord
#print axioms Record.toChecked_slot
#print axioms Record.toChecked_modify
#print axioms Record.toChecked_compute
#print axioms FiniteFix.iterate_relation
#print axioms mixed_exact
#print axioms every_depth_exact
#print axioms paper_record_correspondence
#print axioms source_paper_stable
#print axioms target_observation_stable

end LeanPoo.Tests.PaperRecordDispatch
