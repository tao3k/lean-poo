import LeanPoo.Functional.ContainerValidation

/-! Finite executable alignment: List → named schema → heterogeneous Tuple →
List of Function wrappers, followed by refinement and exact-reference publication.
The host maps vectors to rows and immutable identities to the explicit IDs here. -/
namespace LeanPoo.Examples.ContainerContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata

/-- Dynamic function rows distinguish integer values, Boolean values and arity. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar
  deriving Repr, BEq

abbrev Call := List Scalar → Except String (List Scalar)

/-- A single Integer argument/result row remains unchanged after validation. -/
def integerRow : List Scalar → Except String (List Scalar)
  | [.integer n] => .ok [.integer n]
  | _ => .error "integer row"

/-- A dispatch method returns exactly two ordered values, Integer then Boolean. -/
def dispatchRow : List Scalar → Except String (List Scalar)
  | [.integer n, .flag ready] => .ok [.integer n, .flag ready]
  | _ => .error "dispatch row"

/-- One heterogeneous tuple contains a dispatch Function and a list of Functions. -/
inductive Slot where
  | dispatch : Call → Slot
  | transforms : List Call → Slot

/-- Named schema fields keep the same representation before and after wrapping. -/
structure Task where
  tenant : String
  handlers : List Slot

/-- Wrap the dispatch position through the already proved Function protocol. -/
def dispatchSlot : Slot → Except String Slot
  | .dispatch source => .ok (.dispatch (FunctionValidation.wrap integerRow dispatchRow source))
  | _ => .error "dispatch slot"

/-- Reuse ordered List traversal to wrap every transform without invoking its body. -/
def transformsSlot : Slot → Except String Slot
  | .transforms sources =>
    (ContainerValidation.list
      (fun source => .ok (FunctionValidation.wrap integerRow integerRow source)) sources).map Slot.transforms
  | _ => .error "transforms slot"

/-- Complete structural gating checks both tuple shape and tagged positions. -/
def shape (task : Task) : Except String Unit :=
  match task.handlers with
  | [.dispatch _, .transforms _] => .ok ()
  | _ => .error "task shape"

/-- The typed fixture already fixes its named inventory. Parent tenant policy
and added nonempty-transform policy use the actual existing refine operation. -/
def schema : ObjectContract.Contract Task String Unit String :=
  refine
    {view := ⟨fun _ => true, fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun task path =>
       if task.tenant = "api" then [] else [.rejected (path ++ ["tenant"]) "tenant mismatch"]}
    (fun task path => match task.handlers with
      | [_, .transforms (_ :: _)] => []
      | _ => [.rejected (path ++ ["handlers"]) "missing transform"])

/-- Final schema obligations inspect the fully wrapped tuple and list. -/
def final (task : Task) : Except String Unit :=
  match diagnose schema task [] with
  | [] => .ok ()
  | _ => .error "schema refinement"

/-- Batch tuple normalization precedes whole-object refinement. Failure exposes
no partially installed Task, and the source's function fields remain available. -/
def normalizeTask (task : Task) : Except String Task :=
  validateObject shape
    (fun source => (ContainerValidation.tuple "tuple arity" [dispatchSlot, transformsSlot] source.handlers).map
      (fun handlers => {source with handlers := handlers})) final task

/-- Root lists use complete structural gating before any per-task normalization. -/
def normalizeBatch (tasks : List Task) : Except String (List Task) :=
  ContainerValidation.validate
    (fun source => (Validation.traverse shape source).map fun _ => ())
    (ContainerValidation.list normalizeTask) (fun _ => .ok ()) tasks

/-- Execute both kinds of wrapped callbacks, preserving order and multiple values. -/
def run (task : Task) : Except String Int := do
  match task.handlers with
  | [.dispatch dispatch, .transforms transforms] =>
    let row ← dispatch [.integer 2]
    match row with
    | [.integer units, .flag true] =>
      let result : List Scalar ← transforms.foldlM
        (fun (value : List Scalar) (transform : Call) => transform value) [.integer units]
      match result with
      | [.integer total] => pure total
      | _ => throw "transform result"
    | _ => throw "dispatch result"
  | _ => throw "unchecked task"

/-- Application-owned reference data is separate from authorization. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  totals : List Int
  deriving DecidableEq, Repr

/-- Project only the existing evidence associations used by bindEvidence. -/
def view (result : Result) : Nat × Nat × Nat :=
  (result.subject, result.descriptor, result.context)

/-- Existing application predicates/formula remain effective after exact binding. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"batch", fun _ => True, fun _ => isTrue True.intro⟩
  output := ⟨"totals", fun _ => True, fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Complex finite controls cover nesting, malformed carriers/arity, callback
failures, refinement refusal, raw/stale evidence rejection and current retry. -/
def check : Except String Unit := do
  let dispatch : Call := fun row => do
    let row ← integerRow row
    match row with
    | [.integer n] => pure [.integer (n+1), .flag true]
    | _ => throw "unreachable"
  let double : Call := fun row => match row with
    | [.integer n] => .ok [.integer (2*n)]
    | _ => .error "transform body"
  let increment : Call := fun row => match row with
    | [.integer n] => .ok [.integer (n+1)]
    | _ => .error "transform body"
  let raw : Task := ⟨"api", [.dispatch dispatch, .transforms [double, increment]]⟩
  let batch ← normalizeBatch [raw, raw]
  let totals ← Validation.traverse run batch
  unless totals == [7,7] do throw "container results changed"
  match normalizeBatch [{raw with handlers := [.dispatch dispatch]}] with
  | .error "task shape" => pure ()
  | _ => throw "tuple arity admitted"
  match normalizeTask {raw with handlers := [.dispatch dispatch, .transforms []]} with
  | .error "schema refinement" => pure ()
  | _ => throw "refinement bypassed"
  let broken ← normalizeTask {raw with handlers :=
    [.dispatch (fun _ => .ok [.flag true]), .transforms [double]]}
  match run broken with
  | .error "dispatch row" => pure ()
  | _ => throw "output wrapper bypassed"
  let bound := invocation.bindEvidence 2 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) :=
    .ok (⟨subject,7,context,totals⟩,6)
  match bound.publish 5 (produce 1 5) 2 with
  | (.error .logic,5) => pure ()
  | _ => throw "raw reference admitted"
  match bound.publish 5 (produce 2 4) 2 with
  | (.error .logic,5) => pure ()
  | _ => throw "stale context admitted"
  match bound.publish 5 (produce 2 5) 2 with
  | (.ok result,6) => unless result.totals == [7,7] do throw "retry result changed"
  | _ => throw "current retry rejected"

#eval match check with
  | .ok () => IO.println "CONTAINER-CONTRACTS-OK"
  | .error message => throw (IO.userError message)
#print axioms ContainerValidation.list_positions
#print axioms ContainerValidation.list_length
#print axioms ContainerValidation.list_unchanged
#print axioms ContainerValidation.tuple_arity_error
#print axioms ContainerValidation.tuple_success
#print axioms ContainerValidation.tuple_positions
#print axioms ContainerValidation.accepted
#print axioms ContainerValidation.child_error
#print axioms ContainerValidation.refined
#print axioms validated_binding
end LeanPoo.Examples.ContainerContracts
