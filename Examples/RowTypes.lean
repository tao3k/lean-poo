import LeanPoo.Functional.RowTypes
import LeanPoo.Functional.RecursiveTypes
import LeanPoo.Functional.MethodDeclarations

/-! Object field replacement, inferred row extensions, and guarded finite unfolding.
Names and Function signatures correspond to the Gerbil row service fixture. -/
namespace Examples.RowTypes
open LeanPoo.Functional
open LeanPoo.Functional.PrototypeTypes
open LeanPoo.Functional.RowTypes

/-- Source methods accept Integer arguments and return UInt results. -/
def handler : Ty := .function [.atom .uint] [.atom .integer]
/-- A client only supplies UInt arguments and needs Integer results. -/
def clientHandler : Ty := .function [.atom .integer] [.atom .uint]
/-- A concrete producer declares one extra audit field. -/
def source : Row String Ty := ⟨[("handler", handler), ("audit", .atom .uint)], true⟩
/-- An open interface requires a single safely replaceable method field. -/
def interface : Row String Ty := ⟨[("handler", clientHandler)], false⟩
example : check (PrototypeTypes.check 8) source interface = true := by decide
example : Replaces Subtype source interface :=
  check_sound _ _ (PrototypeTypes.check_sound 8) _ _ (by decide)
/-- Exact closed targets cannot discard producer fields. -/
example : check (PrototypeTypes.check 8) source { interface with closed := true } = false := by decide
/-- Key ordering does not affect exact closed structural replacement. -/
def exactTarget : Row String Ty := ⟨[("audit", .atom .integer), ("handler", clientHandler)], true⟩
example : check (PrototypeTypes.check 8) source exactTarget = true := by decide
/-- Open sources do not promise the absence of extra fields. -/
example : check (PrototypeTypes.check 8) { source with closed := false } exactTarget = false := by decide

/-- Row extension keeps the tail's closure discipline and explicit field names. -/
def explicit : Row String Ty := ⟨[("handler", handler)], false⟩
/-- A disjoint candidate supplies audit metadata rather than replacing the method. -/
def extension : Row String Ty := ⟨[("audit", .atom .integer)], true⟩
example : (splice explicit extension).isOk = true := by decide
example : splice explicit explicit = .error () := by
  simp [splice, explicit, lookup]
/-- Duplicate candidate kinds and colliding rows are invalid before constraints.
The candidate IDs stand for the finite universe used by the Gerbil solver. -/
def kinded (candidate : Nat) : Bool := candidate < 2
/-- Only the audit extension satisfies the exact closed consumer interface. -/
def constraints (candidate : Nat) : Bool := candidate == 0
example : PrototypeTypes.infer (assignmentValid kinded constraints) [0, 1, 2, 3] = .unique 0 := by decide
example : PrototypeTypes.infer (assignmentValid kinded (fun _ => true)) [0, 1, 2, 3] =
    .ambiguous [0, 1] := by decide
/-- A unique row assignment retains both its kind/disjointness and type constraints. -/
example (candidate : Nat)
    (accepted : PrototypeTypes.infer (assignmentValid kinded constraints) [0, 1, 2, 3] = .unique candidate) :
    candidate ∈ [0, 1, 2, 3] ∧ kinded candidate = true ∧ constraints candidate = true :=
  inferred_valid _ _ _ accepted

/-- Small symbolic carrier makes repeated recursive variable substitution visible. -/
inductive Skeleton where
  | never | node (children : List Skeleton)
  deriving Repr
/-- Both children reference the same previous finite approximation. -/
def body (prior : Skeleton) : Skeleton := .node [prior, prior]
example : LeanPoo.Functional.RecursiveTypes.unfold body .never 2 =
    .node [.node [.never, .never], .node [.never, .never]] := rfl
/-- The existing safe recursive interpreter produces exactly the finite type. -/
example : LeanPoo.Prototype.Recursive.solve
    (LeanPoo.Functional.RecursiveTypes.program body .never) 4 3 =
      .value (LeanPoo.Functional.RecursiveTypes.unfold body .never 3) :=
  LeanPoo.Functional.RecursiveTypes.closes body .never 3
/-- Insufficient work never returns the accepted prefix of a recursive schema. -/
example : LeanPoo.Functional.RecursiveTypes.bounded 12 11 body .never 3 = .error () := by
  apply LeanPoo.Functional.RecursiveTypes.exhausted
  decide

/-- An inherited Record view retains its optional audit and exact closed shape. -/
def workerRecord : Row String (Ty × Bool) :=
  ⟨[("run", (handler, false)), ("limit", (.atom .uint, false)), ("audit", (.atom .bool, true))], true⟩

/-- A structural Object client requires its method and numeric limit only. -/
def workerInterface : Row String Ty :=
  ⟨[("limit", .atom .integer), ("run", clientHandler)], false⟩

/-- A concrete closed Object can prove an undeclared optional field is absent. -/
def workerObject : Row String Ty := ⟨[("run", handler), ("limit", .atom .uint)], true⟩

/-- The Record client preserves optional absence without constructing a default. -/
def workerClient : Row String (Ty × Bool) :=
  ⟨[("audit", (.atom .bool, true)), ("run", (clientHandler, false)), ("limit", (.atom .integer, false))], false⟩

example : recordCheck (PrototypeTypes.check 8) (fun _ => false) workerRecord (requiredRow workerInterface) = true := by decide
example : recordCheck (PrototypeTypes.check 8) (fun _ => false) (requiredRow workerObject) workerClient = true := by decide
example : recordCheck (PrototypeTypes.check 8) (fun _ => false) (requiredRow {workerObject with closed := false}) workerClient = false := by decide
example : recordCheck (PrototypeTypes.check 8) (fun _ => false) workerRecord (requiredRow {workerInterface with closed := true}) = false := by decide

/-- Candidate presence is checked jointly with child variance and target closure. -/
def workerLayout (optionalRun : Bool) : Row String (Ty × Bool) :=
  ⟨[("run", (handler, optionalRun)), ("limit", (.atom .uint, false)), ("audit", (.atom .bool, true))], true⟩

/-- One complete declaration chooses the original required-run Record candidate. -/
example : DeclarativeMetadata.inferRowView "Record worker / Object interface"
    (PrototypeTypes.check 8) (fun _ => false) workerLayout (requiredRow workerInterface) [true, false] =
    .ok (.unique false, some ("Record worker / Object interface", false, workerLayout false)) := by rfl

/-- Full declaration provenance composes with universal Record-to-Object reads.
The caller supplies child behavior, including the established Function law. -/
example (accepts : Ty → Value → Prop)
    (sound : ∀ a b, PrototypeTypes.check 8 a b = true → ∀ value, accepts a value → accepts b value)
    (artifact) (published : DeclarativeMetadata.inferRowView "Record worker / Object interface"
      (PrototypeTypes.check 8) (fun _ => false) workerLayout (requiredRow workerInterface) [true, false] =
      .ok (.unique false, some artifact)) :
    artifact = ("Record worker / Object interface", false, workerLayout false) ∧
      ∀ observe, RecordAdmits accepts workerRecord observe → Admits accepts workerInterface observe := by
  obtain ⟨same, included⟩ := DeclarativeMetadata.inferRowView_sound "Record worker / Object interface"
    (PrototypeTypes.check 8) (fun _ => false) workerLayout (requiredRow workerInterface) [true, false] accepts sound (by intro field impossible; contradiction) false artifact published
  refine ⟨same, ?_⟩
  intro observe valid
  exact (requiredRow_admits accepts workerInterface observe).mp (included observe valid)

/-- The reverse direction preserves all Record observations of the same carrier.
Host Class initialization and wrapper effects are separate runtime obligations. -/
example (accepts : Ty → Value → Prop)
    (sound : ∀ a b, PrototypeTypes.check 8 a b = true → ∀ value, accepts a value → accepts b value)
    (observe : String → Option Value) (valid : Admits accepts workerObject observe) :
    RecordAdmits accepts workerClient observe :=
  objectToRecord_sound (PrototypeTypes.check 8) (fun _ => false) accepts sound (by intro field impossible; contradiction) workerObject workerClient (by decide) observe valid

#print axioms lookup_required
#print axioms requiredRow_admits
#print axioms recordToObject_sound
#print axioms objectToRecord_sound
#print axioms DeclarativeMetadata.inferRowView_sound


/-- The finite candidate keeps its retired Slot metadata; only its impossible
payload is evidence of absence. Bool is the deliberately inhabited alternative. -/
def retiredLayout (live : Bool) : Row String (Ty × Bool) :=
  ⟨(requiredRow workerObject).fields ++ [("retired", (if live then .atom .bool else .union [], true))], true⟩

/-- The closed interface forbids an actual retired key, even though the selected
source declares it optional. No field is removed from the candidate artifact. -/
def retiredTarget : Row String (Ty × Bool) := requiredRow {workerInterface with closed := true}

example : recordCheck (PrototypeTypes.check 8) (emptyCheck 8) (retiredLayout false) retiredTarget = true := by decide
example : recordCheck (PrototypeTypes.check 8) (emptyCheck 8) (retiredLayout true) retiredTarget = false := by decide
example : recordCheck (PrototypeTypes.check 8) (emptyCheck 8)
    {retiredLayout false with closed := false} retiredTarget = false := by decide
-- A required target cannot be supplied by an absent optional source.
example : recordCheck (PrototypeTypes.check 8) (emptyCheck 8) (retiredLayout false)
    ⟨retiredTarget.fields ++ [("retired", (.atom .uint, false))], true⟩ = false := by decide
-- An absent optional source need not replace an unrelated optional Function child.
example : recordCheck (PrototypeTypes.check 8) (emptyCheck 8) (retiredLayout false)
    ⟨retiredTarget.fields ++ [("retired", (handler, true))], true⟩ = true := by decide

/-- One whole solve retains the original signature and the complete source layout. -/
example : DeclarativeMetadata.inferRowView "sealed worker" (PrototypeTypes.check 8) (emptyCheck 8)
    retiredLayout retiredTarget [true, false] =
    .ok (.unique false, some ("sealed worker", false, retiredLayout false)) := rfl

/-- Existing finite emptiness laws supply the witness interpretation. Publication
proves both target reads and actual absence, without deleting source metadata. -/
example (model : Interpretation Value) (laws : EmptyLaws model.accepts) (artifact)
    (published : DeclarativeMetadata.inferRowView "sealed worker" (PrototypeTypes.check 8) (emptyCheck 8)
      retiredLayout retiredTarget [true, false] = .ok (.unique false, some artifact)) :
    artifact = ("sealed worker", false, retiredLayout false) ∧
      ∀ observe, RecordAdmits model.accepts (retiredLayout false) observe →
        RecordAdmits model.accepts retiredTarget observe ∧ observe "retired" = none := by
  have emptySound : ∀ field, emptyCheck 8 field = true → ∀ value, ¬ model.accepts field value :=
    fun field checked => (emptyCheck_sound 8 field checked).refuses laws
  obtain ⟨same, included⟩ := DeclarativeMetadata.inferRowView_sound "sealed worker"
    (PrototypeTypes.check 8) (emptyCheck 8) retiredLayout retiredTarget [true, false] model.accepts
    (fun a b checked => PrototypeTypes.replacement model (check_sound 8 a b checked))
    emptySound false artifact published
  refine ⟨same, ?_⟩
  intro observe valid
  refine ⟨included observe valid, ?_⟩
  exact absentField_observe (emptyCheck 8) model.accepts emptySound (.union [], true)
    (observe "retired") (by rfl) (valid.1 "retired" (.union [], true) (by rfl))

#print axioms recordShape_sound
#print axioms absentField_observe
#print axioms record_replacement
#print axioms recordCheck_sound

/-- The primary Gerbil worker consumes Integer and returns checked UInt8;
its backup and target interface use the existing UInt-returning handler. -/
def primaryWorker : Ty := .function [.integerRange { lower := some 0, upper := some 255 }] [.atom .integer]

/-- The host literal tag interpretation supplies Symbol membership. The finite Ty
fixture forgets exact tag literals but retains both original branch identities. -/
def taggedWorkers (bad : Bool) : List (Nat × Ty) :=
  [(0, primaryWorker),
   (1, if bad then .atom .bool else handler)]

/-- Worker consumers require readable tag/value fields and permit extra slots. -/
def taggedWorkerView : Row String (Ty × Bool) :=
  ⟨[("tag", (.atom .symbol, false)), ("value", (handler, false))], false⟩

/-- The tag Type is a faithful host-supplied literal view in the generic theorem;
this concrete Ty projection uses Symbol for both tags, never top or Any. -/
def workerTag (_ : Nat) : Ty := .atom .symbol

/-- All tagged branches use the existing field test and required/open row rule. -/
def taggedWorkersCheck (bad : Bool) : Bool :=
  taggedRowsCheck (PrototypeTypes.check 8) (fun field => emptyCheck 8 field)
    "tag" "value" workerTag (taggedWorkers bad) taggedWorkerView

example : taggedWorkersCheck false = true := by decide
example : taggedWorkersCheck true = false := by decide
example : taggedRowsCheck (PrototypeTypes.check 8) (fun field => emptyCheck 8 field)
    "tag" "value" workerTag (taggedWorkers false) { taggedWorkerView with closed := true } = false := by decide
example : taggedRowsCheck (PrototypeTypes.check 8) (fun field => emptyCheck 8 field)
    "tag" "value" workerTag (taggedWorkers false)
    ⟨("audit", (.atom .uint, true)) :: taggedWorkerView.fields, false⟩ = false := by decide

/-- Complete inference keeps the original branch list in the unique artifact;
an incompatible later branch cannot be hidden by an earlier successful one. -/
example : DeclarativeMetadata.inferDeclared 2 taggedWorkersCheck [true, false]
    (fun bad => (Except.ok ("tagged workers", bad, taggedWorkers bad) :
      Except String (String × Bool × List (Nat × Ty)))) =
    .ok (.unique false, some ("tagged workers", false, taggedWorkers false)) := rfl

/-- Universal readable replacement follows from each selected branch's actual
observations and the same behavioral Function/empty-Type interpretations. -/
example (model : Interpretation Value) (branch : Nat × Ty)
    (present : branch ∈ taggedWorkers false) (observe : String → Option Value)
    (valid : Admits model.accepts
      (taggedRow "tag" "value" (workerTag branch.1) branch.2) observe) :
    RecordAdmits model.accepts taggedWorkerView observe :=
  taggedRowsCheck_sound (PrototypeTypes.check 8) (fun field => emptyCheck 8 field)
    model.accepts (fun a b accepted => PrototypeTypes.replacement model (PrototypeTypes.check_sound 8 a b accepted))
    (fun field accepted => (emptyCheck_sound 8 field accepted).refuses model.emptyLaws)
    "tag" "value" (by decide) workerTag (taggedWorkers false) taggedWorkerView (by decide) branch present observe valid

/-- Prefix binding preserves the original Sum branch order and callback layout. -/
example : substitute (prefixEnvironment [.atom .symbol]
    (fun _ => .sum [0, 1] [primaryWorker, handler])) (.pair (.var 0) (.var 1)) =
    .pair (.atom .symbol) (.sum [0, 1] [primaryWorker, handler]) := by
  simp [substitute, prefixEnvironment]

/-- Actual Sum normalization keeps the original discriminator and exact checked
payload. The checked payload may be a Function wrapper, not the raw procedure. -/
example (lookup : Nat → Option (Value → Except String Value)) (source checked : Nat × Value)
    (accepted : VariantValidation.sum lookup "unknown tag" source = .ok checked) :
    ∃ normalize, lookup source.1 = some normalize ∧
      normalize source.2 = .ok checked.2 ∧ checked.1 = source.1 :=
  VariantValidation.sum_success lookup "unknown tag" source checked accepted

#print axioms taggedRowsCheck_sound

/-- A retired branch retains its tag and nested callback metadata. Only a
positive impossible mandatory payload permits omission from a readable view. -/
def retiredWorkers (live : Bool) : List (Nat × Ty) :=
  (2, if live then .atom .bool else .pair (.union []) handler) :: taggedWorkers false

/-- Complete candidate inference uses the same common row/empty judgments. -/
def retiredWorkersCheck (live : Bool) : Bool :=
  taggedRowsCheck (PrototypeTypes.check 8) (emptyCheck 8)
    "tag" "value" workerTag (retiredWorkers live) taggedWorkerView

example : retiredWorkersCheck false = true := by decide
example : retiredWorkersCheck true = false := by decide
example : taggedRowsCheck (PrototypeTypes.check 8) (emptyCheck 8)
    "tag" "value" workerTag (retiredWorkers false) {taggedWorkerView with closed := true} = false := by decide

/-- An impossible branch does not erase the original candidate or nested
callback signature from the artifact selected by the complete declaration solver. -/
example : DeclarativeMetadata.inferDeclared 2 retiredWorkersCheck [true, false]
    (fun live => (Except.ok ("retired workers", live, retiredWorkers live) :
      Except String (String × Bool × List (Nat × Ty)))) =
    .ok (.unique false, some ("retired workers", false, retiredWorkers false)) := rfl

/-- Every actual selected branch still satisfies the consumer. The empty-payload
case is impossible, using the existing interpretation law, not a sampled value. -/
example (model : Interpretation Value) (branch : Nat × Ty)
    (present : branch ∈ retiredWorkers false) (observe : String → Option Value)
    (valid : Admits model.accepts
      (taggedRow "tag" "value" (workerTag branch.1) branch.2) observe) :
    RecordAdmits model.accepts taggedWorkerView observe :=
  taggedRowsCheck_sound (PrototypeTypes.check 8) (emptyCheck 8)
    model.accepts (fun a b accepted => PrototypeTypes.replacement model (PrototypeTypes.check_sound 8 a b accepted))
    (fun field accepted => (emptyCheck_sound 8 field accepted).refuses model.emptyLaws)
    "tag" "value" (by decide) workerTag (retiredWorkers false) taggedWorkerView
    (by decide) branch present observe valid

end Examples.RowTypes
