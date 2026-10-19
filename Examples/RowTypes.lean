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

example : recordCheck (PrototypeTypes.check 8) workerRecord (requiredRow workerInterface) = true := by decide
example : recordCheck (PrototypeTypes.check 8) (requiredRow workerObject) workerClient = true := by decide
example : recordCheck (PrototypeTypes.check 8) (requiredRow {workerObject with closed := false}) workerClient = false := by decide
example : recordCheck (PrototypeTypes.check 8) workerRecord (requiredRow {workerInterface with closed := true}) = false := by decide

/-- Candidate presence is checked jointly with child variance and target closure. -/
def workerLayout (optionalRun : Bool) : Row String (Ty × Bool) :=
  ⟨[("run", (handler, optionalRun)), ("limit", (.atom .uint, false)), ("audit", (.atom .bool, true))], true⟩

/-- One complete declaration chooses the original required-run Record candidate. -/
example : DeclarativeMetadata.inferRowView "Record worker / Object interface"
    (PrototypeTypes.check 8) workerLayout (requiredRow workerInterface) [true, false] =
    .ok (.unique false, some ("Record worker / Object interface", false, workerLayout false)) := by rfl

/-- Full declaration provenance composes with universal Record-to-Object reads.
The caller supplies child behavior, including the established Function law. -/
example (accepts : Ty → Value → Prop)
    (sound : ∀ a b, PrototypeTypes.check 8 a b = true → ∀ value, accepts a value → accepts b value)
    (artifact) (published : DeclarativeMetadata.inferRowView "Record worker / Object interface"
      (PrototypeTypes.check 8) workerLayout (requiredRow workerInterface) [true, false] =
      .ok (.unique false, some artifact)) :
    artifact = ("Record worker / Object interface", false, workerLayout false) ∧
      ∀ observe, RecordAdmits accepts workerRecord observe → Admits accepts workerInterface observe := by
  obtain ⟨same, included⟩ := DeclarativeMetadata.inferRowView_sound "Record worker / Object interface"
    (PrototypeTypes.check 8) workerLayout (requiredRow workerInterface) [true, false] accepts sound false artifact published
  refine ⟨same, ?_⟩
  intro observe valid
  exact (requiredRow_admits accepts workerInterface observe).mp (included observe valid)

/-- The reverse direction preserves all Record observations of the same carrier.
Host Class initialization and wrapper effects are separate runtime obligations. -/
example (accepts : Ty → Value → Prop)
    (sound : ∀ a b, PrototypeTypes.check 8 a b = true → ∀ value, accepts a value → accepts b value)
    (observe : String → Option Value) (valid : Admits accepts workerObject observe) :
    RecordAdmits accepts workerClient observe :=
  objectToRecord_sound (PrototypeTypes.check 8) accepts sound workerObject workerClient (by decide) observe valid

#print axioms lookup_required
#print axioms requiredRow_admits
#print axioms recordToObject_sound
#print axioms objectToRecord_sound
#print axioms DeclarativeMetadata.inferRowView_sound

end Examples.RowTypes
