import LeanPoo.Functional.ValidationRebinding
import LeanPoo.Functional.FunctionValidation

/-! Finite receiver-bound counterpart of computed-publication: inherited run,
Function dependency capture, checked hook replacement, nested result Functions,
refinement and exact evidence. Reference tokens have supplied host correspondence;
JSON, arbitrary callbacks/mutation and host cache implementation are not proved. -/
namespace LeanPoo.Examples.ComputedContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata
open Prototype.Recursive

/-- Dynamic Function rows distinguish Boolean from Integer values. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar
  deriving BEq, Repr
abbrev Call := List Scalar → Except String (List Scalar)

/-- Exactly one Integer is admitted before and after each transform. -/
def row : List Scalar → Except String (List Scalar)
  | [.integer n] => .ok [.integer n]
  | _ => .error "integer row"

/-- Tokens expose aliasing in this fixture without deciding function equality. -/
inductive Value where
  | integer : Int → Value
  | function : Nat → Call → Value
  | callbacks : List (Nat × Call) → Value
  | maker : (List Scalar → Except String Call) → Value

/-- All names correspond to the inherited service's computed dependency graph. -/
inductive Key where
  | backend | bias | captured | run | callbacks | maker
  deriving DecidableEq, BEq, Repr
abbrev Program := Generator Key Value

/-- The Type wrapper is reused for defaults, dependencies and Function lists. -/
def wrap (source : Call) : Call := FunctionValidation.wrap row row source

/-- Use a normalized function's checked single result. -/
def invoke (source : Call) (n : Int) : Except String Int := do
  let result ← source [.integer n]
  match result with | [.integer total] => pure total | _ => throw "result row"

/-- Captured aliases are Any-typed; callable/list/maker slots have recursive
validators. A maker validates both its argument and each returned Function. -/
def validate : Key → Value → Interaction Key Value Value
  | .backend, .function token source | .run, .function token source => .value (.function (token+100) (wrap source))
  | .callbacks, .callbacks entries => .value (.callbacks (entries.map (fun entry => (entry.1+100,wrap entry.2))))
  | .maker, .maker source => .value (.maker (FunctionValidation.wrap row (fun result => .ok (wrap result)) source))
  | .captured, value => .value value
  | .bias, .integer n => .value (.integer n)
  | _, _ => .error "slot type"

/-- The inherited base run captures final-self backend and bias requests. The
child adds a second bias using ordinary inherited computation composition. -/
def service (revised : Bool) : Program
  | .backend => .value (.function (if revised then 9 else 1) (fun args => match args with
      | [.integer n] => .ok [.integer (if revised then n*2 else n+1)]
      | _ => .error "raw backend"))
  | .bias => .value (.integer (if revised then 3 else 2))
  | .captured => .call .backend .value
  | .run => .call .backend (fun backend => .call .bias (fun bias =>
      match backend, bias with
      | .function _ dependency, .integer offset =>
        let inherited : Call := fun args => do
          let [.integer n] := args | throw "raw run"
          let total ← invoke dependency n
          pure [.integer (total+offset)]
        .value (.function 2 (fun args => do
          let total ← inherited args
          let [.integer n] := total | throw "inherited result"
          pure [.integer (n+offset)]))
      | _, _ => .error "dependency type"))
  | .callbacks => .call .backend (fun backend => .call .run (fun run =>
      match backend, run with
      | .function first f, .function second g => .value (.callbacks [(first,f),(second,g)])
      | _, _ => .error "callback dependency"))
  | .maker => .call .backend (fun backend => .call .bias (fun bias =>
      match backend, bias with
      | .function _ dependency, .integer offset => .value (.maker (fun args => do
        let [.integer extra] := args | throw "maker argument"
        pure (fun args => do
          let [.integer n] := args | throw "maker result argument"
          let total ← invoke dependency n
          pure [.integer (total+offset+extra)])))
      | _, _ => .error "maker dependency"))

/-- The existing safe recursive closure binds every request to checked values. -/
def program (revised : Bool) := ValidationRebinding.rebind (service revised) validate

/-- Budget exhaustion remains a refusal, never successful or divergent evaluation. -/
def read (revised : Bool) (key : Key) : Except String Value :=
  match solve (program revised) 12 key with
  | .value value => .ok value
  | .error cause => .error cause
  | .pending => .error "unfinished"

/-- The alias theorem applies to this actual computed source and selected Type. -/
theorem captured_checked (revised : Bool) (depth : Nat) (value : Value)
    (found : solve (program revised) depth .backend = .value value) :
    solve (program revised) (depth+1) .captured = .value value :=
  ValidationRebinding.alias_value (service revised) validate depth .captured .backend value rfl (fun _ => rfl) found

/-- The final object reference is supplied separately from the callable carrier. -/
structure Subject where
  reference : Nat
  revised : Bool
  backend : Value
  captured : Value
  run : Value
  callbacks : Value
  maker : Value

/-- Observe only supplied identity tokens; this is not host function equality. -/
def token : Value → Option Nat | .function identity _ => some identity | _ => none

/-- Root refinement requires captured and public backend associations to agree. -/
def schema : ObjectContract.Contract Subject String Unit String :=
  refine
    {view := ⟨fun _ => true, fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun value path => if token value.backend == token value.captured then []
      else [.rejected path "computed dependency"])

/-- Complete rebound reads precede final refinement on one assembled record. -/
def normalize (source : Subject) : Except String Subject :=
  validateObject (fun _ => .ok ()) (fun value => do
    let backend ← read value.revised .backend
    let captured ← read value.revised .captured
    let run ← read value.revised .run
    let callbacks ← read value.revised .callbacks
    let maker ← read value.revised .maker
    pure {value with reference := value.reference+1, backend, captured, run, callbacks, maker})
    (fun value => if (diagnose schema value []).isEmpty then .ok () else .error "refinement") source

/-- The checked hook changes the dependency generator; final initialization must
rebuild captures rather than retain the earlier checked field values. -/
def factory := ClassValidation.instantiate normalize
  (some (fun value => .ok {value with revised := true}))

/-- Evidence retains the exact normalized root/context association. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  total : Int
  deriving DecidableEq, Repr

/-- Bind only the existing identity/context projections. -/
def view (value : Result) : Nat × Nat × Nat := (value.subject,value.descriptor,value.context)

/-- Application authorization remains independent of evidence association. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"service",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"result",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Match the Scheme inherited/hook workflow, nested Function checks, certified
shared memo, refinement and rejected raw/stale evidence followed by current retry. -/
def test : Except String Unit := do
  let raw : Subject := ⟨1,false,.integer 0,.integer 0,.integer 0,.integer 0,.integer 0⟩
  let checked ← factory raw
  unless checked.revised && token checked.backend == some 109 && token checked.captured == some 109 do
    throw "dependency not rebound"
  let .function _ run := checked.run | throw "missing run"
  let .callbacks callbacks := checked.callbacks | throw "missing callbacks"
  let first ← invoke run 2
  let total ← callbacks.foldlM (fun n entry => invoke entry.2 n) first
  unless total == 46 do throw "inherited pipeline"
  let .maker maker := checked.maker | throw "missing maker"
  let nested ← maker [.integer 1]
  unless (← invoke nested 2) == 8 do throw "nested output"
  match nested [.flag false] with
  | .error "integer row" => pure () | _ => throw "nested guard bypassed"
  let (receipt, cache) ← (Cached.runCertified (program true) .captured 100 {}).mapError (fun _ => "memo failed")
  let (_, reused) ← (Cached.runCertified (program true) .backend 100 cache).mapError (fun _ => "reuse failed")
  unless reused.statistics.hits > cache.statistics.hits do throw "shared memo missed"
  unless receipt.result.observation matches .value (.function 109 _) do throw "raw memo captured"
  let bound := invocation.bindEvidence checked.reference 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) := .ok (⟨subject,7,context,total⟩,6)
  match bound.publish 5 (produce raw.reference 5) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "raw evidence accepted"
  match bound.publish 5 (produce checked.reference 4) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "stale evidence accepted"
  match bound.publish 5 (produce checked.reference 5) checked.reference with
  | (.ok _,6) => pure () | _ => throw "current retry refused"

#eval match test with
  | .ok () => IO.println "COMPUTED-CONTRACTS-OK"
  | .error cause => throw (IO.userError cause)
#print axioms captured_checked
#print axioms ValidationRebinding.interpret_bind
#print axioms ValidationRebinding.step
#print axioms ValidationRebinding.dependency
#print axioms ValidationRebinding.alias_value
#print axioms ValidationRebinding.dependency_error
#print axioms ValidationRebinding.direct_value
#print axioms ValidationRebinding.source_error
#print axioms ValidationRebinding.checked_error
#print axioms ValidationRebinding.inherited
#print axioms ValidationRebinding.memo_agrees
#print axioms ValidationRebinding.batch_error
#print axioms ClassValidation.initialized_refinement
#print axioms validated_binding
end LeanPoo.Examples.ComputedContracts
