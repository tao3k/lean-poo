import LeanPoo.Object.Migration
import LeanPoo.Object.Definition

namespace LeanPoo.Tests.ClassMigration

inductive V1 where
  | name | absent
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
inductive V2 where
  | name | age | retired | summary
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
inductive V3 where
  | fullName | ageText | email | summary | unknown
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value1 (_ : V1) := String
abbrev Value2 : V2 → Type
  | .age => Nat
  | _ => String
abbrev Value3 (_ : V3) := String

private def person1 : Object.ClassSpec V1 Value1 :=
  { name := "Person.v1", sealed := true, rules := [{ key := .name }] }
private def person2 : Object.ClassSpec V2 Value2 :=
  { name := "Person.v2", sealed := true, rules :=
      [{ key := .name }, { key := .age, default := some 0, accepts := (· ≤ 120) },
       { key := .retired, optional := true },
       { key := .summary, compute := some (.self fun self => do
           let name ← self .name
           let age ← self .age
           return s!"v2:{name}/{age}") }] }
private def person3 : Object.ClassSpec V3 Value3 :=
  { name := "Person.v3", sealed := true, rules :=
      [{ key := .fullName }, { key := .ageText, default := some "0", accepts := (·.toNat?.isSome) },
       { key := .email, default := some "default@example" },
       { key := .summary, compute := some (.self fun self => do
           let name ← self .fullName
           let age ← self .ageText
           let email ← self .email
           return s!"v3:{name}/{age}/{email}") }] }

private def first : Except C4.Error (Object.Memoized V1 Value1) := do
  let base ← person1.instantiate
  base.extend "Ada.v1" (Object.Declaration.empty.withValue .name "Ada")

private def toV2 : List (Object.FieldTransfer V1 Value1 V2 Value2) :=
  [Object.FieldTransfer.preserve .name .name rfl]
private def toV3 : List (Object.FieldTransfer V2 Value2 V3 Value3) :=
  [Object.FieldTransfer.preserve .name .fullName rfl,
   { source := .age, target := .ageText, convert := fun age => .ok (toString age) }]

private def lifecycle (mode : Object.ResolutionMode) : Except String Bool := do
  let original ← first.mapError (fun _ => "v1")
  let original := original.plan.memoizeUsing mode
  let second ← (person2.migrateFrom "Ada.v2" original toV2).mapError (fun _ => "v2")
  let edited ← (second.object.reviseDeclaration "Ada.v2" fun declaration =>
    (declaration.withValue .age 42).withValue .retired "old data").mapError (fun _ => "edit")
  let third ← (person3.migrateFrom "Ada.v3" edited toV3).mapError (fun _ => "v3")
  let future ← (third.object.extend "Grace.v3"
    (Object.Declaration.empty.withValue .fullName "Grace")).mapError (fun _ => "future")
  return original.read .name == some "Ada" && original.read .absent == none &&
    second.object.read .name == some "Ada" && second.object.read .age == some 0 &&
    second.object.read .summary == some "v2:Ada/0" &&
    edited.read .retired == some "old data" && edited.read .summary == some "v2:Ada/42" &&
    third.object.read .fullName == some "Ada" && third.object.read .ageText == some "42" &&
    third.object.read .email == some "default@example" &&
    third.object.read .summary == some "v3:Ada/42/default@example" &&
    future.read .summary == some "v3:Grace/42/default@example" &&
    original.mode == mode && second.object.mode == mode && third.object.mode == mode &&
    person1.acceptsObject original && person2.acceptsObject edited &&
    (LeanPoo.allSlots third.object.plan).length == 4 &&
    edited.read .retired == some "old data"

#guard [.onDemand, .compiled, .indexed].all fun mode =>
  match lifecycle mode with | .ok true => true | _ => false

private def nameToFull : Object.FieldTransfer V1 Value1 V3 Value3 :=
  Object.FieldTransfer.preserve .name .fullName rfl
private def missingEmail (policy : Object.MissingSourcePolicy) :
    Object.FieldTransfer V1 Value1 V3 Value3 :=
  Object.FieldTransfer.preserve .absent .email rfl policy

private def fallback : Except String Bool := do
  let source ← first.mapError (fun _ => "source")
  let result ← (person3.migrateFrom "Fallback" source
    [nameToFull, missingEmail .useTargetDefault]).mapError (fun _ => "fallback")
  return result.object.read .email == some "default@example" &&
    result.object.read .ageText == some "0"
#guard match fallback with | .ok true => true | _ => false

#guard match first with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Missing" source [nameToFull, missingEmail .reject] with
    | .error (.missingSource .absent) => true | _ => false

#guard match first with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Required" source
      [Object.FieldTransfer.preserve .absent .fullName rfl .useTargetDefault] with
    | .error (.targetRejected "Person.v3") => true | _ => false

#guard match first with
  | .error _ => false
  | .ok source => match person2.migrateFrom "BadConversion" source
      [Object.FieldTransfer.preserve .name .name rfl,
       { source := .name, target := .age, convert := fun text =>
           match text.toNat? with
           | some age => .ok age | none => .error "not a natural" }] with
    | .error (.conversionFailed .name .age "not a natural") => true | _ => false

#guard match first with
  | .error _ => false
  | .ok source => match person3.migrateFrom "BadRefinement" source
      [nameToFull, { source := .name, target := .ageText, convert := fun _ => .ok "invalid" }] with
    | .error (.targetRejected "Person.v3") => true | _ => false

-- The complete transfer shape and identity are checked before any source
-- read. Even a valid first transfer must not force this broken source field.
private def hazardous : Except C4.Error (Object.Memoized V1 Value1) :=
  Object.define "Unread" do
    Object.Declaration.Builder.slot .name (.thunk fun _ => panic! "unexpected source read")

#guard match hazardous with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Duplicate" source [nameToFull, nameToFull] with
    | .error (.duplicateTarget .fullName) => true | _ => false
#guard match hazardous with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Unknown" source
      [nameToFull, Object.FieldTransfer.preserve .name .unknown rfl] with
    | .error (.unknownTarget .unknown) => true | _ => false
#guard match hazardous with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Computed" source
      [nameToFull, Object.FieldTransfer.preserve .name .summary rfl] with
    | .error (.nonDataTarget .summary) => true | _ => false
#guard match hazardous with
  | .error _ => false
  | .ok source => match person3.migrateFrom "Person.v3" source [nameToFull] with
    | .error (.graph (.duplicateNode "Person.v3")) => true | _ => false

private def fixedEmail : Object.ClassSpec V3 Value3 :=
  person3.derive "Fixed" [Object.SlotRule.constant .email "fixed@example"]
#guard match hazardous with
  | .error _ => false
  | .ok source => match fixedEmail.migrateFrom "Fixed instance" source
      [nameToFull, Object.FieldTransfer.preserve .name .email rfl] with
    | .error (.nonDataTarget .email) => true | _ => false

-- No implicit same-name copying: the target's defaults apply unless a
-- transfer is supplied, and required data without a transfer is rejected.
#guard match first with
  | .error _ => false
  | .ok source => match person2.migrateFrom "NoTransfers" source [] with
    | .error (.targetRejected "Person.v2") => true | _ => false

example (result : Object.Migrated person3) : person3.acceptsObject result.object = true :=
  result.accepted

#print axioms Object.FieldTransfer.evaluate_preserve

end LeanPoo.Tests.ClassMigration
