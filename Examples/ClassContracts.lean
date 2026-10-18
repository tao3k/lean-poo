import LeanPoo.Functional.ClassValidation
import LeanPoo.Functional.FunctionValidation
import LeanPoo.Functional.PrototypeTypes

/-! Finite counterpart of the inherited service Record: selected defaults,
computed audit, checked initialization, nested plugins, refinement and binding.
C3 resolution, JSON, host identity and mutable getters are supplied boundaries.
The callback/slot interpretation advances the generalized descriptor future work. -/
namespace LeanPoo.Examples.ClassContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata

/-- Dynamic rows distinguish Boolean values from Integer arguments/results. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar
  deriving BEq, Repr

abbrev Call := List Scalar → Except String (List Scalar)

/-- Exactly one Integer is admitted on this side of the Function boundary. -/
def integerRow : List Scalar → Except String (List Scalar)
  | [.integer n] => .ok [.integer n]
  | _ => .error "integer row"

/-- The inherited computed audit has a distinct Boolean result signature. -/
def booleanRow : List Scalar → Except String (List Scalar)
  | [.flag b] => .ok [.flag b]
  | _ => .error "boolean row"

/-- Procedures remain opaque; no decision procedure for function equality is used. -/
inductive Value where
  | integer : Int → Value
  | function : Call → Value

/-- Selected metadata checks the field category before wrapper construction. -/
def callable : Value → Bool | .function _ => true | _ => false

/-- Reuse Function validation for inherited defaults, overrides and list children. -/
def wrap (output : List Scalar → Except String (List Scalar)) : Value → Except String Value
  | .function source => .ok (.function (FunctionValidation.wrap integerRow output source))
  | _ => .error "not callable"

/-- Class metadata has already selected run's interface; optional presence is
checked here and defaults are provisioned separately by the factory. -/
def transform : ClassValidation.Slot Value String := ⟨false, fun _ => true, wrap integerRow⟩

/-- Optional absence bypasses the same reusable child validator. -/
def optionalTransform : ClassValidation.Slot Value String := {transform with optional := true}

/-- A finite record fixes its inventory, while its dynamic field categories and
Function call boundaries still require explicit admission. -/
structure Service where
  reference : Nat
  tenant : String
  limit : Int
  bias : Int
  run : Option Value
  audit : Value
  plugins : List Value

/-- The existing Class prototype supplies inherited run/audit/default values.
The computed audit captures unchanged scalar state, not arbitrary mutable getters. -/
def defaults (plugins : List Value := []) : Service :=
  ⟨1, "api", 10, 2, some (.function (fun args => match args with
    | [.integer n] => .ok [.integer (n+1)] | _ => .error "raw run")),
    .function (fun args => match args with
      | [.integer n] => .ok [.flag (n ≤ 10)] | _ => .error "raw audit"), plugins⟩

/-- Complete structure admission happens before any field normalizer. -/
def shape (value : Service) : Except String Unit :=
  if value.run.any callable && callable value.audit && value.plugins.all callable then .ok ()
  else .error "record shape"

/-- Normalize the complete field batch, then assign one new reference token.
Its correspondence to persistent host identity is a fixture premise. -/
def fields (value : Service) : Except String Service := do
  let run ← ClassValidation.normalize transform "missing run" "constant" value.run
  let audit ← wrap booleanRow value.audit
  let plugins ← Validation.traverse (wrap integerRow) value.plugins
  pure {value with reference := value.reference+1, run, audit, plugins}

/-- A refined schema relates the final record to the api service configuration. -/
def schema : ObjectContract.Contract Service String Unit String :=
  refine
    {view := ⟨fun _ => true, fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun value path => if value.tenant == "api" && value.bias ≤ value.limit then []
      else [.rejected path "service relation"])

/-- Final refinement receives the installed checked record, never raw fields. -/
def validate := validateObject shape fields
  (fun value => if (diagnose schema value []).isEmpty then .ok () else .error "service relation")

/-- Invoke a normalized transform and require exactly one Integer result. -/
def invoke (value : Value) (n : Int) : Except String Int := do
  let .function callback := value | throw "not callable"
  let result ← callback [.integer n]
  match result with | [.integer total] => pure total | _ => throw "result row"

/-- Initialization sees a checked run and returns an override for final validation. -/
def hook (checked : Service) : Except String Service := do
  let some run := checked.run | throw "missing run"
  pure {checked with run := some (.function (fun args => do
    let [.integer n] := args | throw "hook input"
    let total ← invoke run n
    pure [.integer (total+checked.bias)]))}

/-- The full factory validates defaults, invokes the hook, then validates again. -/
def factory := ClassValidation.instantiate validate (some hook)

/-- Execute inherited methods and normalized plugin lists before computed audit. -/
def consume (service : Service) : Except String (Int × Bool) := do
  let some run := service.run | throw "missing run"
  let first ← invoke run 2
  let total ← service.plugins.foldlM (fun n plugin => invoke plugin n) first
  let .function audit := service.audit | throw "missing audit"
  let [.flag approved] ← audit [.integer total] | throw "audit row"
  pure (total, approved)

/-- Identity associations are fixture data, not producer authentication. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  total : Int
  deriving DecidableEq, Repr

/-- Exact binding projects all three supplied associations. -/
def view (result : Result) : Nat × Nat × Nat := (result.subject,result.descriptor,result.context)

/-- Application authorization remains separate from reference binding. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"service",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"result",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Executable positive/negative controls mirror defaults, inheritance selection,
recursive wrapping, hook replacement, refinement, evidence refusal and retry. -/
def test : Except String Unit := do
  let double := Value.function (fun args => match args with
    | [.integer n] => .ok [.integer (n*2)] | _ => .error "raw double")
  let checked ← factory (defaults [double])
  unless (← consume checked) == (10,true) do throw "factory result"
  let some (.function run) := checked.run | throw "missing wrapped run"
  match run [.flag false] with
  | .error "integer row" => pure () | _ => throw "input escaped"
  let selected := ClassValidation.resolve "run" [("run",false),("run",true),("limit",true)]
  unless selected == some false do throw "child override lost"
  match ClassValidation.normalize optionalTransform "missing" "constant" none with
  | .ok none => pure () | _ => throw "optional absence"
  match ClassValidation.normalize transform "missing" "constant" none with
  | .error "missing" => pure () | _ => throw "required absence"
  let constant : ClassValidation.Slot Int String := ⟨false, (· == 1), fun n => .ok (n+1)⟩
  match ClassValidation.normalize constant "missing" "constant" (some 1) with
  | .error "constant" => pure () | _ => throw "constant weakened"
  match factory {defaults [] with bias := 11} with
  | .error _ => pure () | _ => throw "refinement bypassed"
  let broken ← factory (defaults [.function (fun _ => .ok [.flag false])])
  match consume broken with
  | .error "integer row" => pure () | _ => throw "output escaped"
  let badHook : Service → Except String Service := fun value => .ok {value with run := some (.integer 3)}
  match ClassValidation.instantiate validate (some badHook) (defaults []) with
  | .error "record shape" => pure () | _ => throw "hook replacement escaped"
  let bound := invocation.bindEvidence checked.reference 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) := .ok (⟨subject,7,context,10⟩,6)
  match bound.publish 5 (produce 1 5) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "raw evidence accepted"
  match bound.publish 5 (produce checked.reference 4) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "stale evidence accepted"
  match bound.publish 5 (produce checked.reference 5) checked.reference with
  | (.ok _,6) => pure () | _ => throw "retry refused"

#eval match test with
  | .ok () => IO.println "CLASS-CONTRACTS-OK"
  | .error message => throw (IO.userError message)
#print axioms ClassValidation.optional_absent
#print axioms ClassValidation.required_absent
#print axioms ClassValidation.raw_constant_error
#print axioms ClassValidation.child_error
#print axioms ClassValidation.checked_constant_error
#print axioms ClassValidation.present_success
#print axioms ClassValidation.override_selected
#print axioms ClassValidation.inherited_selected
#print axioms ClassValidation.initial_error
#print axioms ClassValidation.no_hook
#print axioms ClassValidation.hook_sequence
#print axioms ClassValidation.hook_error
#print axioms ClassValidation.initialized_final
#print axioms ClassValidation.initialized_membership
#print axioms ClassValidation.initialized_refinement
#print axioms validateObject_refine
#print axioms validated_binding
/-- The same explicit required/optional record signature used by the Gerbil
factory after the ground Self prefix is fixed. Field labels are finite IDs. -/
def inferredRecord (self super : PrototypeTypes.Ty) : ClassValidation.RecordType Nat PrototypeTypes.Ty :=
  ⟨[(0, .function [self] [super], false), (1, .atom .uint, false),
    (2, .atom .uint, false), (3, .function [self] [super], true)], false⟩
example : ClassValidation.recordCheck (PrototypeTypes.check 8)
    (inferredRecord (.atom .uint) (.atom .integer))
    (inferredRecord (.atom .integer) (.atom .uint)) = true := by decide
example : ClassValidation.recordCheck (PrototypeTypes.check 8)
    (⟨[(0, .atom .uint, true)], true⟩ : ClassValidation.RecordType Nat PrototypeTypes.Ty)
    ⟨[(0, .atom .integer, false)], false⟩ = false := by decide
example : ClassValidation.recordCheck (PrototypeTypes.check 8)
    (⟨[(0, .atom .uint, false)], false⟩ : ClassValidation.RecordType Nat PrototypeTypes.Ty)
    ⟨[(0, .atom .uint, false)], true⟩ = false := by decide
/-- The prefix fixes Self to UInt; the argument and callback variance together
force the same Super = Integer as the executable Gerbil call observation. -/
def recordCandidateValid (super : PrototypeTypes.Ty) : Bool :=
  PrototypeTypes.check 8 (.atom .uint) super &&
  PrototypeTypes.check 8 (.atom .integer) super &&
  ClassValidation.recordCheck (PrototypeTypes.check 8)
    (inferredRecord (.atom .uint) super) (inferredRecord (.atom .uint) (.atom .integer))
example : PrototypeTypes.infer recordCandidateValid [.atom .uint, .atom .integer] =
    .unique (.atom .integer) := by
  have bad : recordCandidateValid (.atom .uint) = false := by decide
  have good : recordCandidateValid (.atom .integer) = true := by decide
  simp [PrototypeTypes.infer, bad, good]
/-- A selected complete inference assignment derives the entire record signature
as one shared obligation. This reuses the finite search rather than a field solver. -/
example (candidates : List (Nat → PrototypeTypes.Ty)) (target : ClassValidation.RecordType Nat PrototypeTypes.Ty)
    (accepted : PrototypeTypes.infer (fun env => ClassValidation.recordCheck (PrototypeTypes.check 8)
        (inferredRecord (env 0) (env 1)) target) candidates = .unique env) :
    (target.closed = true → (inferredRecord (env 0) (env 1)).closed = true) ∧
      ClassValidation.RecordFieldsReplace PrototypeTypes.Subtype
        (inferredRecord (env 0) (env 1)).fields target.fields := by
  exact ClassValidation.recordCheck_sound _ _ (PrototypeTypes.check_sound 8) _ _
    (PrototypeTypes.infer_unique _ _ accepted).2
/-- Optional absence remains absence, and cannot satisfy a required target. -/
example : ClassValidation.slotAdmits (fun (_ : Unit) (n : Nat) => n > 0) () true none := rfl
example : ¬ ClassValidation.slotAdmits (fun (_ : Unit) (n : Nat) => n > 0) () false none := by simp [ClassValidation.slotAdmits]
#print axioms ClassValidation.recordFieldsCheck_sound
#print axioms ClassValidation.recordCheck_sound
#print axioms ClassValidation.record_field_replacement
end LeanPoo.Examples.ClassContracts
