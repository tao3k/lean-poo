import LeanPoo.Prototype.RecordDispatch
import LeanPoo.Prototype.FiniteFix

/-! The paper's x/y/z record with z as integral complex coordinates. The
source calculation reads final self through an error-propagating dispatcher;
the typed target retains x/y as integers and z as an integer pair. -/

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperRecordComplexRelation

inductive Key where
  | x | y | z | other (name : String)
  deriving DecidableEq

private abbrev Value : Key → Type
  | .x | .y => Int
  | .z => Int × Int
  | .other _ => Unit

private abbrev Error := String × String
private abbrev Source := CheckedRecord Key Value Error
private abbrev Target := Record Key Value

private def missing : Key → Error
  | .x => ("unbound slot", "x")
  | .y => ("unbound slot", "y")
  | .z => ("unbound slot", "z")
  | .other name => ("unbound slot", name)

private def sourceBase : Source
  | .x => .ok 1
  | .y => .ok 2
  | key => .error (missing key)

private theorem sourceBase_canonical :
    ∀ key error, sourceBase key = .error error → error = missing key := by
  intro key error h
  cases key <;> simp [sourceBase] at h ⊢
  all_goals cases h; rfl

private def targetBase : Target := sourceBase.toRecord

private theorem base_exact : targetBase.toChecked missing = sourceBase :=
  CheckedRecord.toChecked_toRecord sourceBase missing sourceBase_canonical

private def sourceX3 : Proto Source Source Source :=
  fun _ inherited => CheckedRecord.slot .x (3 : Int) inherited

private def sourceDouble : Proto Source Source Source :=
  fun _ inherited => CheckedRecord.modify .x (· * 2) inherited

private def targetX3 : Proto Target Target Target := Record.slot .x (3 : Int)
private def targetDouble : Proto Target Target Target := Record.modify .x (· * 2)

private def sourceZValue (self : Source) : Except Error (Int × Int) := do
  let x ← self .x
  let y ← self .y
  return (x, y)

private def targetZValue (self : Target) : Int × Int :=
  ((self.lookup .x).getD 0, (self.lookup .y).getD 0)

private def sourceZ : Proto Source Source Source :=
  fun self inherited => CheckedRecord.computeM .z sourceZValue self inherited

private def targetZ : Proto Target Target Target := Record.compute .z targetZValue

private def sourceLayers : Proto Source Source Source :=
  compose sourceZ (compose sourceDouble sourceX3)

private def targetLayers : Proto Target Target Target :=
  compose targetZ (compose targetDouble targetX3)

/-- Exact checked observations plus the two final-self reads needed by z. -/
private def Related (source : Source) (target : Target) : Prop :=
  target.toChecked missing = source ∧
    (∃ x, source .x = .ok x) ∧ source .y = .ok 2

private theorem base_related : Related sourceBase targetBase := by
  exact ⟨base_exact, ⟨1, rfl⟩, rfl⟩

private theorem mixed_exact (sourceSelf : Source) (targetSelf : Target) :
    ((compose targetDouble targetX3) targetSelf targetBase).toChecked missing =
      (compose sourceDouble sourceX3) sourceSelf sourceBase := by
  simp only [compose, targetDouble, targetX3, sourceDouble, sourceX3,
    Record.toChecked_modify, Record.toChecked_slot, base_exact]

private theorem sourceZValue_exact (sourceSelf : Source) (targetSelf : Target)
    (related : targetSelf.toChecked missing = sourceSelf)
    (x : Int) (hx : sourceSelf .x = .ok x) (hy : sourceSelf .y = .ok 2) :
    sourceZValue sourceSelf = .ok (targetZValue targetSelf) := by
  have targetX : targetSelf.lookup .x = some x := by
    have value : targetSelf.toChecked missing .x = .ok x :=
      (congrFun related .x).trans hx
    cases lookup : targetSelf.lookup .x with
    | none => simp [Record.toChecked, lookup] at value
    | some candidate =>
      simp [Record.toChecked, lookup] at value
      cases value
      rfl
  have targetY : targetSelf.lookup .y = some (2 : Int) := by
    have value : targetSelf.toChecked missing .y = .ok 2 :=
      (congrFun related .y).trans hy
    cases lookup : targetSelf.lookup .y with
    | none => simp [Record.toChecked, lookup] at value
    | some candidate =>
      simp [Record.toChecked, lookup] at value
      cases value
      rfl
  simp [sourceZValue, hx, hy, targetZValue, targetX, targetY]
  rfl

private theorem step_related (sourceSelf : Source) (targetSelf : Target)
    (related : Related sourceSelf targetSelf) :
    Related (sourceLayers sourceSelf sourceBase)
      (targetLayers targetSelf targetBase) := by
  obtain ⟨same, ⟨x, hx⟩, hy⟩ := related
  have calculation := sourceZValue_exact sourceSelf targetSelf same x hx hy
  have exact : (targetLayers targetSelf targetBase).toChecked missing =
      sourceLayers sourceSelf sourceBase := by
    exact Record.toChecked_computeM .z targetZValue sourceZValue
      targetSelf ((compose targetDouble targetX3) targetSelf targetBase)
      sourceSelf ((compose sourceDouble sourceX3) sourceSelf sourceBase)
      missing calculation (mixed_exact sourceSelf targetSelf)
  refine ⟨exact, ⟨6, ?_⟩, ?_⟩
  · rfl
  · rfl

/-- The paper's checked x/y/z calculation and the typed record agree for
every key, including unknown keys, at every finite unfolding depth. -/
private theorem every_depth_related (depth : Nat) :
    Related (FiniteFix.iterate sourceLayers sourceBase sourceBase depth)
      (FiniteFix.iterate targetLayers targetBase targetBase depth) :=
  FiniteFix.iterate_relation sourceLayers targetLayers Related
    sourceBase targetBase sourceBase targetBase base_related step_related depth

private theorem every_depth_exact (depth : Nat) :
    (FiniteFix.iterate targetLayers targetBase targetBase depth).toChecked missing =
      FiniteFix.iterate sourceLayers sourceBase sourceBase depth :=
  (every_depth_related depth).1

private theorem source_stable :
    FiniteFix.iterate sourceLayers sourceBase sourceBase 2 =
      FiniteFix.iterate sourceLayers sourceBase sourceBase 3 := by
  funext key
  cases key <;> rfl

private def sourceFixed : { value : Source // sourceLayers value sourceBase = value } :=
  FiniteFix.certified sourceLayers sourceBase sourceBase 2 source_stable

private theorem target_observation_stable (extra : Nat) :
    (FiniteFix.iterate targetLayers targetBase targetBase (2 + extra)).toChecked missing =
      (FiniteFix.iterate targetLayers targetBase targetBase 2).toChecked missing := by
  rw [every_depth_exact, every_depth_exact]
  exact FiniteFix.stable_forever sourceLayers sourceBase sourceBase 2 source_stable extra

private def observed :=
  (FiniteFix.iterate targetLayers targetBase targetBase 2).toChecked missing

#guard (observed .x) matches .ok 6
#guard (observed .y) matches .ok 2
#guard (observed .z) matches .ok (6, 2)
#guard (observed (.other "missing")) matches .error ("unbound slot", "missing")
#guard (sourceZValue (fun key => match key with
  | .x => .error (missing .x)
  | .y => .ok 2
  | .z => .error (missing .z)
  | .other name => .error (missing (.other name)))) matches
    .error ("unbound slot", "x")
#guard (sourceZValue (fun key => match key with
  | .x => .ok 6
  | .y => .error (missing .y)
  | .z => .error (missing .z)
  | .other name => .error (missing (.other name)))) matches
    .error ("unbound slot", "y")

#eval IO.println "POOF-RECORD-COMPLEX-RELATION-OK allKeys=true allDepths=true z=(6,2) checkedErrors=true stableDepth=2"
#print axioms Record.toChecked_computeM
#print axioms every_depth_related
#print axioms every_depth_exact
#print axioms source_stable
#print axioms target_observation_stable

end LeanPoo.Tests.PaperRecordComplexRelation
