import LeanPoo.Functional.VariantValidation

/-! Finite alignment of Pair → Map → Sum → ordered Union → refined Function.
Table equivalence/order and host reference identities are supplied interpretations. -/
namespace LeanPoo.Examples.VariantContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata

/-- Dynamic callback rows retain argument/result type and arity distinctions. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar
  deriving BEq, Repr

abbrev Call := List Scalar → Except String (List Scalar)

/-- Integer callbacks take and return exactly one integer. -/
def integerRow : List Scalar → Except String (List Scalar)
  | [.integer n] => .ok [.integer n]
  | _ => .error "integer row"

/-- Approval callbacks return one Boolean after their integer input. -/
def booleanRow : List Scalar → Except String (List Scalar)
  | [.flag ready] => .ok [.flag ready]
  | _ => .error "boolean row"

/-- A tagged payload may contain a named schema, a bare Function or disabled data. -/
inductive Payload where
  | schema : String → Call → Payload
  | function : Call → Payload
  | integer : Int → Payload

/-- Ordered Union alternatives are distinct from tagged Sum selection. -/
inductive Branch where
  | schema | function

/-- The finite schema keeps the existing parent/refine discipline. Its named
inventory is fixed by the typed constructor; dynamic inventory is proved elsewhere. -/
def schema : ObjectContract.Contract Payload String Unit String :=
  refine
    {view := ⟨(fun value => match value with | .schema _ _ => true | _ => false),
       fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun value path => match value with
      | .schema tenant _ => if tenant.isEmpty then [.rejected path "empty tenant"] else []
      | _ => [.rejected path "schema shape"])

/-- Structural matching selects without running whole-schema obligations. -/
def branchShape : Branch → Payload → Bool
  | .schema, .schema _ _ => true
  | .function, .function _ => true
  | _, _ => false

/-- Final membership belongs to the selected branch, after normalization. -/
def branchMember : Branch → Payload → Bool
  | .schema, value => (diagnose schema value []).isEmpty
  | .function, .function _ => true
  | _, _ => false

/-- Wrap the chosen procedure through the existing Function validator. -/
def checkBranch : Branch → Payload → Except String Payload
  | .schema, .schema tenant source =>
    let checked := Payload.schema tenant (FunctionValidation.wrap integerRow integerRow source)
    if (diagnose schema checked []).isEmpty then .ok checked else .error "schema refinement"
  | .function, .function source => .ok (.function (FunctionValidation.wrap integerRow integerRow source))
  | _, _ => .error "branch shape"

/-- Only a known Sum tag selects its payload Type; no execution fallback exists. -/
def operation (source : String × Payload) : Except String (String × Payload) :=
  VariantValidation.sum
    (fun tag => if tag == "active" then
       some (VariantValidation.union branchShape branchMember checkBranch "union missing" "union invalid" [.schema,.function])
     else if tag == "disabled" then
       some (fun value => match value with | .integer n => .ok (.integer n) | _ => .error "disabled payload")
     else none) "unknown tag" source

abbrev Routes := List (String × (String × Payload)) × Call

/-- Complete routing structure is checked before recursive normalization. -/
def shape (source : Routes) : Except String Unit :=
  if source.1.all (fun entry => match entry.2 with
    | ("active", .schema _ _) | ("active", .function _) | ("disabled", .integer _) => true
    | _ => false) then .ok () else .error "routing shape"

/-- Reuse root refinement for the cross-route tenant policy of the fixed api fixture. -/
def routing : ObjectContract.Contract Routes String Unit String :=
  refine
    {view := ⟨fun _ => true, fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun source path => if source.1.all (fun entry => match entry.2 with
      | ("active", .schema tenant _) => tenant == "api"
      | _ => true) then [] else [.rejected path "tenant mismatch"])

/-- Pair/Map/Sum/Union normalization completes before root refinement and binding. -/
def normalize (source : Routes) : Except String Routes :=
  validateObject shape
    (VariantValidation.pair
      (VariantValidation.map Except.ok operation (fun a b => a == b) "key collision")
      (fun approval => .ok (FunctionValidation.wrap integerRow booleanRow approval)))
    (fun checked => if (diagnose routing checked []).isEmpty then .ok () else .error "routing refinement") source

/-- Route names, rather than host-table iteration order, determine execution order. -/
def run (source : Routes) : Except String (List Int × Bool) := do
  let totals ← Validation.traverse (fun name => do
    let some entry := source.1.lookup name | throw "route missing"
    match entry with
    | ("disabled", .integer n) => pure n
    | ("active", .schema _ callback) | ("active", .function callback) =>
      let row ← callback [.integer 2]
      match row with | [.integer n] => pure n | _ => throw "route result"
    | _ => throw "route shape") ["primary", "secondary"]
  let approval ← source.2 [.integer (totals.foldl (· + ·) 0)]
  match approval with
  | [.flag ready] => pure (totals, ready)
  | _ => throw "approval result"

/-- Immutable evidence associations are data, not proof of producer authenticity. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  totals : List Int
  approved : Bool
  deriving DecidableEq, Repr

/-- Expose exactly the producer's recorded subject/descriptor/context. -/
def view (result : Result) : Nat × Nat × Nat := (result.subject,result.descriptor,result.context)

/-- Existing application policy remains in force after exact binding. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"routes", fun _ => True, fun _ => isTrue True.intro⟩
  output := ⟨"routing result", fun _ => True, fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Complex controls exercise route dispatch, Sum data, invalid tags, Map collision,
committed Union failure, callback refusal, root refinement and bound retry. -/
def check : Except String Unit := do
  let increment : Call := fun row => match row with
    | [.integer n] => .ok [.integer (n+1)] | _ => .error "source argument"
  let double : Call := fun row => match row with
    | [.integer n] => .ok [.integer (n*2)] | _ => .error "source argument"
  let approval : Call := fun row => match row with
    | [.integer n] => .ok [.flag (n < 10)] | _ => .error "approval argument"
  let raw : Routes := ([("primary",("active",.schema "api" increment)),
                         ("secondary",("active",.function double))],approval)
  let checked ← normalize raw
  let (totals, ready) ← run checked
  unless totals == [3,4] && ready do throw "routing result changed"
  let disabled ← normalize ([("primary",("active",.schema "api" increment)),
                             ("secondary",("disabled",.integer 4))],approval)
  let (disabledTotals, _) ← run disabled
  unless disabledTotals == [3,4] do throw "disabled data changed"
  match operation ("unknown",.integer 0) with
  | .error "unknown tag" => pure () | _ => throw "unknown tag accepted"
  match VariantValidation.map (fun _ : String => .ok "same")
      (fun n : Nat => .ok n) (fun a b => a == b) "collision" [("A",1),("a",2)] with
  | .error "collision" => pure () | _ => throw "normalized keys overwritten"
  match VariantValidation.union (fun _ _ => true) (fun _ _ => true)
      (fun branch (n : Nat) => if branch then .error "selected failure" else .ok n)
      "missing" "invalid" [true,false] 1 with
  | .error "selected failure" => pure () | _ => throw "Union fell through"
  match normalize ([("primary",("active",.schema "other" increment))],approval) with
  | .error "routing refinement" => pure () | _ => throw "root refinement bypassed"
  let broken ← normalize ([("primary",("active",.function (fun _ => .ok [.flag true]))),
                            ("secondary",("disabled",.integer 4))],approval)
  match run broken with
  | .error "integer row" => pure () | _ => throw "output wrapper bypassed"
  let bound := invocation.bindEvidence 2 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) :=
    .ok (⟨subject,7,context,totals,ready⟩,6)
  match bound.publish 5 (produce 1 5) 2 with
  | (.error .logic,5) => pure () | _ => throw "raw reference accepted"
  match bound.publish 5 (produce 2 4) 2 with
  | (.error .logic,5) => pure () | _ => throw "stale context accepted"
  match bound.publish 5 (produce 2 5) 2 with
  | (.ok _,6) => pure () | _ => throw "current retry failed"

#eval match check with
  | .ok () => IO.println "VARIANT-CONTRACTS-OK"
  | .error message => throw (IO.userError message)
#print axioms VariantValidation.pair_success
#print axioms VariantValidation.pair_left_error
#print axioms VariantValidation.distinctKeys_head
#print axioms VariantValidation.map_success
#print axioms VariantValidation.map_positions
#print axioms VariantValidation.map_child_error
#print axioms VariantValidation.map_collision
#print axioms VariantValidation.sum_unknown
#print axioms VariantValidation.sum_selected
#print axioms VariantValidation.sum_error
#print axioms VariantValidation.sum_tag_preserved
#print axioms VariantValidation.select_head
#print axioms VariantValidation.select_next
#print axioms VariantValidation.union_missing
#print axioms VariantValidation.union_error
#print axioms VariantValidation.union_selected
#print axioms validateObject_refine
#print axioms validated_binding
/-- A backend snapshot carries callable fields; rebuilding retains the actual
normalizing wrappers. Lists model ordered bindings, not a host tree layout. -/
def ledgerSource : List (Nat × Call) := [(1, fun _ => .ok [.flag false])]

/-- Reuse the existing Function boundary for the table's value descriptor. -/
def ledgerValue (callback : Call) : Except String Call :=
  .ok (FunctionValidation.wrap integerRow integerRow callback)

/-- Persistent table admission composes snapshot normalization and reconstruction. -/
def admitLedger (source : List (Nat × Call)) : Except String (List (Nat × Call)) :=
  VariantValidation.table Except.ok Except.ok (fun key => .ok key) ledgerValue source

/-- A checked lookup cannot bypass an invalid Function result; raw source remains
an independently callable value. No function equality or callback termination is assumed. -/
example : (admitLedger ledgerSource).bind (fun entries => entries.head!.2 [.integer 2]) =
    .error "integer row" := rfl

/-- Normalization may change keys; collision refusal suppresses the consumer. -/
example : VariantValidation.map (fun (key : Int) => .ok key.natAbs)
    (fun (value : Nat) => .ok (value + 1)) (· == ·) "collision" [(-1, 10), (1, 20)] =
    .error "collision" := rfl

/-- Key failure precedes value normalization; the exact failure survives retry
preparation without replacing the old collection. -/
example : VariantValidation.tableRevision
    (fun source : List (Nat × Nat) => VariantValidation.table Except.ok Except.ok
      (fun key => if key = 2 then .error "key-refused" else .ok key)
      (fun value => .ok (value + 1)) source)
    [(1, 10), (2, 20)] = (.error "key-refused", [(1, 10), (2, 20)]) := rfl

/-- Rebuilding may reorder keys after normalization while retaining each checked
value. Consumers must not pair old/new physical iteration positions by index. -/
example : VariantValidation.table (Error := String) Except.ok (fun entries => .ok entries.reverse)
    (fun (key : Int) => .ok (-key)) (fun (value : Nat) => .ok (value + 1))
    [(1, 10), (3, 30)] = .ok [(-3, 31), (-1, 11)] := rfl

#print axioms VariantValidation.tableMaterialize_sound
#print axioms VariantValidation.table_shape_refused
#print axioms VariantValidation.table_positions
#print axioms VariantValidation.table_rebuild_refused
#print axioms VariantValidation.table_refused
#print axioms VariantValidation.table_consumer_refused
#print axioms VariantValidation.tableRevision_refused
end LeanPoo.Examples.VariantContracts
