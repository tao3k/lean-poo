import LeanPoo.Functional.OptionalValidation

/-! Finite alignment: Maybe List of Tuple/TypeValuePair plugins, optional fallback,
root refinement and normalized-reference binding. The host supplies identities;
JSON/configuration parsing and the record inventory are outside this fixture. -/
namespace LeanPoo.Examples.OptionalContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata

/-- Dynamic function rows distinguish integers from Boolean arguments/results. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar
  deriving BEq, Repr

abbrev Call := List Scalar → Except String (List Scalar)

/-- Each transform uses exactly one Integer input and output. -/
def row : List Scalar → Except String (List Scalar)
  | [.integer n] => .ok [.integer n]
  | _ => .error "integer row"

/-- Distinct physical sentinels model void and #f; procedures remain opaque values. -/
inductive Value where
  | missing | falseValue
  | function : Call → Value
  | integer : Int → Value

/-- Dynamic descriptors are reference tokens, including an unrelated valid Type. -/
inductive Descriptor where
  | transform | other | invalid
  deriving BEq, DecidableEq

/-- Maybe's void predicate is independent of OrFalse's #f predicate. -/
def missing : Value → Bool | .missing => true | _ => false

/-- Only #f is absent for the outer OrFalse fallback. -/
def falseValue : Value → Bool | .falseValue => true | _ => false

/-- Carried Type validity is checked before its payload. -/
def valid : Descriptor → Bool | .invalid => false | _ => true

/-- Function membership recognizes a procedure, without promising future calls. -/
def member : Descriptor → Value → Bool
  | .transform, .function _ => true
  | .other, _ => true
  | _, _ => false

/-- A finite structural checker precedes actual Function wrapping. -/
def shape (descriptor : Descriptor) (value : Value) : Except String Unit :=
  if member descriptor value then .ok () else .error "payload shape"

/-- Transform descriptors install the existing checked Function wrapper. -/
def checkValue : Descriptor → Value → Except String Value
  | .transform, .function source => .ok (.function (FunctionValidation.wrap row row source))
  | .other, value => .ok value
  | _, _ => .error "payload validation"

/-- The exact carried Type is retained alongside its normalized payload. -/
def typed := OptionalValidation.typed valid shape member checkValue "invalid Type" "invalid result"

abbrev Plugin := String × (Descriptor × Value)

/-- Structural list/tuple shape is fixed by the typed fixture; dynamic descriptor
validity and each raw payload still require explicit checks before normalization. -/
def pluginsShape (plugins : Option (List Plugin)) : Except String Unit := do
  match plugins with
  | none => pure ()
  | some values =>
    let _ ← Validation.traverse (fun entry =>
      if valid entry.2.1 then shape entry.2.1 entry.2.2 else .error "invalid Type") values
    pure ()

/-- The selected List child accepts complete typed rows, not outer void. -/
def pluginsMember : Option (List Plugin) → Bool
  | none => false
  | some values => values.all (fun entry => valid entry.2.1 && member entry.2.1 entry.2.2)

/-- Reuse the same optional normalizer and ordered child traversal as Scheme. -/
def normalizePlugins := OptionalValidation.normalize Option.isNone pluginsMember pluginsShape
  (fun source => match source with
    | none => .error "present List missing"
    | some values => (Validation.traverse (fun entry => (typed entry.2).map (entry.1, ·)) values).map some)
  "invalid List result"

/-- Inner Maybe accepts void; present values still belong to the Transform Type. -/
def fallbackMember (value : Value) : Bool := missing value || member .transform value

/-- Both sentinel branches avoid their corresponding child operation. -/
def fallbackShape (value : Value) : Except String Unit :=
  if falseValue value || missing value then .ok () else shape .transform value

/-- Outer OrFalse and inner Maybe share one carrier while keeping distinct guards. -/
def normalizeFallback := OptionalValidation.normalize falseValue fallbackMember fallbackShape
  (OptionalValidation.normalize missing (member .transform) (shape .transform) (checkValue .transform) "invalid transform")
  "invalid Maybe result"

/-- Named fields and references are explicit; no equality on functions is required. -/
structure Input where
  reference : Nat
  plugins : Option (List Plugin)
  fallback : Value

/-- The fixed api consumer owns which otherwise valid carried Types it can execute. -/
def schema : ObjectContract.Contract Input String Unit String :=
  refine
    {view := ⟨fun _ => true, fun _ => true, fun _ => [], fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun source path => if source.plugins.toList.all (fun values => values.all
      (fun entry => entry.1 == "api" && entry.2.1 == .transform)) then []
      else [.rejected path "plugin interface"])

/-- Known Function normalizers change references; absent/unchanged fields keep
original reference IDs in this fixture. The host correspondence is a premise. -/
def changes (source : Input) : Bool :=
  source.plugins.toList.any (fun values => values.any (fun entry => match entry.2 with
    | (.transform, .function _) => true | _ => false)) ||
  match source.fallback with | .function _ => true | _ => false

/-- Complete admission normalizes all fields before actual root refinement. -/
def normalize (source : Input) : Except String Input :=
  validateObject
    (fun value => do pluginsShape value.plugins; fallbackShape value.fallback)
    (fun value => do
      let plugins ← normalizePlugins value.plugins
      let fallback ← normalizeFallback value.fallback
      pure ⟨if changes value then 2 else value.reference, plugins, fallback⟩)
    (fun value => if (diagnose schema value []).isEmpty then .ok () else .error "plugin interface") source

/-- Apply one checked Function and retain its normalized single result. -/
def applyValue (value : Value) (n : Int) : Except String Int := do
  let .function callback := value | throw "non-callable"
  let result ← callback [.integer n]
  match result with | [.integer total] => pure total | _ => throw "transform result"

/-- The pipeline matches Scheme: missing list skips plugins, #f/void skip fallback. -/
def run (source : Input) : Except String Int := do
  let total ← (source.plugins.getD []).foldlM (fun n entry => applyValue entry.2.2 n) 2
  match source.fallback with
  | .falseValue | .missing => pure total
  | other => applyValue other total

/-- Application result associations remain data rather than producer authentication. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  total : Int
  deriving Repr, DecidableEq

/-- Project only existing identity/context fields for the binding rule. -/
def view (value : Result) : Nat × Nat × Nat := (value.subject,value.descriptor,value.context)

/-- Application admission remains effective independently of exact binding. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"pipeline",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"total",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Execute sentinel distinctions, selected-child refusal, dependent Type retention,
full pipeline/refinement, callback failure and raw/stale binding refusal/retry. -/
def test : Except String Unit := do
  let increment : Call := fun values => match values with
    | [.integer n] => .ok [.integer (n+1)] | _ => .error "source argument"
  let double : Call := fun values => match values with
    | [.integer n] => .ok [.integer (n*2)] | _ => .error "source argument"
  let source : Input := ⟨1, some [("api",(.transform,.function increment)),
    ("api",(.transform,.function double))], .function increment⟩
  let checked ← normalize source
  unless (← run checked) == 7 do throw "pipeline changed"
  for sentinel in [Value.missing, Value.falseValue] do
    let empty ← normalize ⟨1,none,sentinel⟩
    unless (← run empty) == 2 && empty.reference == 1 do throw "absence changed"
  let carried ← typed (.transform, .function increment)
  unless carried.1 == .transform do throw "carried Type changed"
  match OptionalValidation.normalize falseValue (member .transform) (shape .transform)
      (fun _ => .ok .falseValue) "invalid selected result" (.function increment) with
  | .error "invalid selected result" => pure () | _ => throw "sentinel erased invalid result"
  match typed (.invalid, .function increment) with
  | .error "invalid Type" => pure () | _ => throw "invalid carried Type accepted"
  match normalize {source with plugins := some [("api",(.other,.function increment))]} with
  | .error "plugin interface" => pure () | _ => throw "consumer interface bypassed"
  let broken ← normalize {source with plugins := some [("api",(.transform,.function (fun _ => .ok [.flag false])))]}
  match run broken with
  | .error "integer row" => pure () | _ => throw "callback result bypassed"
  let bound := invocation.bindEvidence checked.reference 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) := .ok (⟨subject,7,context,7⟩,6)
  match bound.publish 5 (produce 1 5) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "raw evidence accepted"
  match bound.publish 5 (produce checked.reference 4) checked.reference with
  | (.error .logic,5) => pure () | _ => throw "stale evidence accepted"
  match bound.publish 5 (produce checked.reference 5) checked.reference with
  | (.ok _,6) => pure () | _ => throw "current retry refused"

#eval match test with
  | .ok () => IO.println "OPTIONAL-CONTRACTS-OK"
  | .error message => throw (IO.userError message)
#print axioms OptionalValidation.absent
#print axioms OptionalValidation.shape_error
#print axioms OptionalValidation.child_error
#print axioms OptionalValidation.selected
#print axioms OptionalValidation.success
#print axioms OptionalValidation.invalid_type
#print axioms OptionalValidation.descriptor_preserved
#print axioms OptionalValidation.typed_requirements
#print axioms OptionalValidation.typed_selected
#print axioms OptionalValidation.typed_error
#print axioms validateObject_refine
#print axioms validated_binding

/-- A finite explicit catalog uses the same dependent Function normalizer. -/
def catalog := OptionalValidation.catalogTyped [Descriptor.transform] shape member checkValue
  "outside catalog" "invalid result"

example : OptionalValidation.catalogCovers [Descriptor.transform]
    [.other, .transform] = true := by decide
example : OptionalValidation.catalogCovers [Descriptor.transform] [.other] = false := by decide
example : catalog (.other, .integer 7) = .error "outside catalog" := by
  apply OptionalValidation.catalogTyped_missing
  simp

example (source checked : Descriptor × Value) (accepted : catalog source = .ok checked) :
    checked.1 = source.1 ∧ source.1 ∈ [Descriptor.transform] ∧ member source.1 checked.2 = true :=
  OptionalValidation.catalogTyped_sound _ _ _ _ _ _ _ _ accepted

example (source target : List Descriptor) (predicate : Descriptor → Value → Prop)
    (value : Descriptor × Value) (covered : OptionalValidation.catalogCovers source target = true)
    (accepted : OptionalValidation.CatalogAdmits source predicate value) :
    OptionalValidation.CatalogAdmits target predicate value :=
  OptionalValidation.catalog_replacement _ _ _ _ covered accepted

#print axioms OptionalValidation.catalogCovers_sound
#print axioms OptionalValidation.catalog_replacement
#print axioms OptionalValidation.catalogTyped_missing
#print axioms OptionalValidation.catalogTyped_sound
#print axioms OptionalValidation.catalog_stale

/-- Dynamic aliases share one captured descriptor token; fresh scopes remain
separate even when a Class/Schema has the same public metadata. -/
def capturedTransform : OptionalValidation.CatalogType Descriptor := ⟨7, .transform⟩
example : OptionalValidation.catalogIdentity capturedTransform ⟨7, .transform⟩ = true := by decide
example : OptionalValidation.catalogIdentity capturedTransform ⟨8, .transform⟩ = false := by decide
example : OptionalValidation.catalogIdentity capturedTransform ⟨7, .other⟩ = false := by decide

example : OptionalValidation.captureCatalog
    (fun (key : Nat) => if key = 0 then (.ok Descriptor.transform : Except String Descriptor) else .error "getter")
    [0, 1] (fun _ => .ok ()) = .error "getter" := by rfl
example : OptionalValidation.captureCatalog
    (fun (_ : Nat) => (.ok Descriptor.transform : Except String Descriptor))
    [0, 1] (fun _ => .error "source drift") = .error "source drift" := by rfl

/-- Provider selection, Class Slot metadata and shared approval are independent
finite stamp positions. A later revision prevents publication of old artifacts. -/
example : OptionalValidation.catalogCall ([0, 0, 0] : List Nat) [0, 0, 0]
    (fun _ => (.ok (19, [0, 1, 0]) : Except String (Nat × List Nat))) "stale" = .error "stale" := by rfl
example (action : Unit → Except String (Nat × List Nat)) :
    OptionalValidation.catalogCall ([0, 0, 0] : List Nat) [0, 0, 1] action "stale" = .error "stale" :=
  OptionalValidation.catalogCall_stale _ _ _ _ (by decide)

/-- Under unchanged sources the exact dependent Function wrapper and original
child errors pass through; this is not a proof of arbitrary Schema predicates. -/
example (source : Descriptor × Value) :
    OptionalValidation.catalogCall ([2, 3, 4] : List Nat) [2, 3, 4]
      (fun _ => (catalog source).map fun checked => (checked, [2, 3, 4])) "stale" = catalog source :=
  OptionalValidation.catalogCall_stable _ _ _

#print axioms OptionalValidation.catalogIdentity_sound
#print axioms OptionalValidation.catalogIdentity_scope
#print axioms OptionalValidation.captureCatalog_sound
#print axioms OptionalValidation.captureCatalog_error
#print axioms OptionalValidation.catalogCall_stale
#print axioms OptionalValidation.catalogCall_error
#print axioms OptionalValidation.catalogCall_changed
#print axioms OptionalValidation.catalogCall_stable
#print axioms OptionalValidation.catalogCall_sound
-- Exhaustive Boolean coverage uses false as the sentinel and true as payload.
#guard OptionalValidation.finiteCoverage (fun value : Bool => !value) id [false, true]

-- A false-only observation cannot certify the missing true payload branch.
#guard !OptionalValidation.finiteCoverage (fun value : Bool => !value) (fun _ => false) [false, true]

/-- Different sentinels compose only when both void and false remain admitted. -/
example (value : Option Bool) :
    OptionalValidation.Admits (fun item => decide (item = none))
      (fun item => item = some false ∨ item = some true) value →
    OptionalValidation.Admits (fun item => decide (item = some false))
      (fun item => item = none ∨ item = some true) value := by
  apply OptionalValidation.sentinel_replacement
  · intro item missing
    have same : item = none := of_decide_eq_true missing
    exact .inr (.inl same)
  · intro item valid
    rcases valid with negative | positive
    · exact .inl (by simp [negative])
    · exact .inr (.inr positive)

/-- One complete solve retains captured signature metadata and the chosen nesting. -/
example : OptionalValidation.inferOptional "optional handler"
    (fun candidate : Nat => decide (candidate = 2))
    (fun candidate => decide (candidate ≤ 2)) [1, 2, 3] =
    .ok (.unique 2, some ("optional handler", 2)) := rfl

#print axioms OptionalValidation.payload_replacement
#print axioms OptionalValidation.sentinel_replacement
#print axioms OptionalValidation.finiteCoverage_sound
#print axioms OptionalValidation.inferOptional_sound

/-- OrFalse's false and Exactly true together cover precisely both Bool values. -/
example (value : Bool) (valid : OptionalValidation.Admits
    (fun item => !item) (fun item => item = true) value) :
    value = false ∨ value = true := by
  apply OptionalValidation.replacement_into (fun item : Bool => !item)
    (fun item => item = true) (fun item => item = false ∨ item = true) _ _ value valid
  · intro item missing
    cases item <;> simp_all
  · intro item present
    exact .inr present

/-- Empty payloads do not erase Maybe's void inhabitant. Unit admits that value. -/
example (value : Option Empty) (valid : OptionalValidation.Admits
    Option.isNone (fun _ => False) value) : value = none := by
  apply OptionalValidation.replacement_into Option.isNone (fun _ => False)
    (fun item : Option Empty => item = none) _ _ value valid
  · intro item missing
    cases item <;> simp_all
  · intro _ impossible
    exact impossible.elim

/-- A false-only target cannot replace Maybe even with a completely empty child. -/
example : ¬ (∀ value : Option Bool,
    OptionalValidation.Admits Option.isNone (fun _ => False) value → value = some false) := by
  intro included
  have missing := included none (.inl rfl)
  cases missing

/-- A normalized decision/ack packet retains its checked callback. Only the
original optional fields are read; no replacement wrapper or carrier is created. -/
example (handler : Call) (decision : Bool) (ack : Option Empty)
    (decisionOK : OptionalValidation.Admits (fun item => !item) (fun item => item = true) decision)
    (ackOK : OptionalValidation.Admits Option.isNone (fun _ => False) ack) :
    (handler, decision, ack).1 = handler ∧ (decision = false ∨ decision = true) ∧ ack = none := by
  refine ⟨rfl, ?_, ?_⟩
  · cases decision <;> simp
  · rcases ackOK with missing | impossible
    · cases ack <;> simp_all
    · exact impossible.elim

/-- Successful normalization proves target membership for the returned value,
including a checked Function, under the original sentinel and child premises. -/
example (source checked : Value) (accepted : OptionalValidation.normalize falseValue
    (member .transform) (shape .transform) (checkValue .transform) "invalid" source = .ok checked) :
    checked = .falseValue ∨ ∃ procedure, checked = .function procedure := by
  apply OptionalValidation.normalized_replacement falseValue (member .transform)
    (shape .transform) (checkValue .transform) "invalid" source checked
    (fun value => value = .falseValue ∨ ∃ procedure, value = .function procedure) _ _ accepted
  · intro value absent
    cases value <;> simp_all [falseValue]
  · intro value present
    cases value <;> simp_all [member]

#print axioms OptionalValidation.replacement_into
#print axioms OptionalValidation.replacement_into_iff
#print axioms OptionalValidation.normalized_replacement
#print axioms OptionalValidation.inferOptional_replacement


/-- Live and retired fields retain their exact dependent directory metadata.
The inhabited alternative cannot be forgotten by the sealed target. -/
def pluginCatalogLayout (liveRetired : Bool) : RowTypes.Row String (List Descriptor × Bool) :=
  ⟨[("active", ([.transform], false)),
    ("retired", (if liveRetired then [.transform] else [], true))], true⟩

/-- The sealed client keeps the active Type token and never invents a retired value. -/
def pluginCatalogTarget : RowTypes.Row String (List Descriptor × Bool) :=
  ⟨[("active", ([.transform], false))], true⟩

/-- The existing complete declaration search composes identity-based catalog
coverage with the shared absence witness, without a catalog-specific solver. -/
example : inferRowView "plugin directory" OptionalValidation.catalogCovers List.isEmpty
    pluginCatalogLayout pluginCatalogTarget [true, false] =
    .ok (.unique false, some ("plugin directory", false, pluginCatalogLayout false)) := rfl

/-- Catalog emptiness supplies a universal witness without executing a payload
predicate. Complete publication retains the original active/retired layout and
proves both readable target membership and the actual absent observation. -/
example (artifact)
    (published : inferRowView "plugin directory" OptionalValidation.catalogCovers List.isEmpty
      pluginCatalogLayout pluginCatalogTarget [true, false] = .ok (.unique false, some artifact)) :
    artifact = ("plugin directory", false, pluginCatalogLayout false) ∧
      ∀ observe, RowTypes.RecordAdmits (fun types value => OptionalValidation.CatalogAdmits types
        (fun tag item => member tag item = true) value) (pluginCatalogLayout false) observe →
      RowTypes.RecordAdmits (fun types value => OptionalValidation.CatalogAdmits types
        (fun tag item => member tag item = true) value) pluginCatalogTarget observe ∧ observe "retired" = none := by
  let accepts := fun types value => OptionalValidation.CatalogAdmits types (fun tag item => member tag item = true) value
  have emptySound : ∀ types, types.isEmpty = true → ∀ value, ¬ accepts types value :=
    fun types checked => OptionalValidation.catalogEmpty_sound types _ checked
  obtain ⟨same, included⟩ := inferRowView_sound "plugin directory" OptionalValidation.catalogCovers List.isEmpty
    pluginCatalogLayout pluginCatalogTarget [true, false] accepts
    (fun source target covered value valid => OptionalValidation.catalog_replacement source target
      (fun tag item => member tag item = true) value covered valid)
    emptySound false artifact published
  refine ⟨same, ?_⟩
  intro observe valid
  refine ⟨included observe valid, ?_⟩
  exact RowTypes.absentField_observe List.isEmpty accepts emptySound ([], true)
    (observe "retired") (by rfl) (valid.1 "retired" ([], true) (by rfl))

/-- Empty directory refusal takes precedence over either possible child error. -/
example (source : Descriptor × Value) :
    OptionalValidation.catalogTyped [] (fun _ _ => .error "shape") (fun _ _ => false)
      (fun _ _ => .error "payload") "missing Type" "bad result" source = .error "missing Type" :=
  OptionalValidation.catalogTyped_empty [] _ _ _ _ _ source rfl

/-- A false payload is an actual inhabitant under its original selected Type. -/
example : OptionalValidation.CatalogAdmits [.other] (fun tag item => member tag item = true)
    (.other, .falseValue) := by simp [OptionalValidation.CatalogAdmits, member]

/-- A live Function directory is inhabited without assuming equality of functions. -/
example : OptionalValidation.CatalogAdmits [.transform] (fun tag item => member tag item = true)
    (.transform, .function row) := by simp [OptionalValidation.CatalogAdmits, member]

#print axioms OptionalValidation.catalogEmpty_sound
#print axioms OptionalValidation.catalogTyped_empty

end LeanPoo.Examples.OptionalContracts
