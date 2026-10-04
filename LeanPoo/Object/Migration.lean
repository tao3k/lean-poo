import LeanPoo.Object.Class

/-! The chapter 6 class-redefinition exercise: explicit field transfers
between typed schemas, fresh target computations, and checked acceptance. -/

namespace LeanPoo.Object

universe u v w x

inductive MissingSourcePolicy where
  | reject
  | useTargetDefault
  deriving Repr, DecidableEq

inductive MigrationError (SourceKey : Type u) (TargetKey : Type w) where
  | duplicateTarget (key : TargetKey)
  | unknownTarget (key : TargetKey)
  | nonDataTarget (key : TargetKey)
  | missingSource (key : SourceKey)
  | conversionFailed (source : SourceKey) (target : TargetKey) (reason : String)
  | graph (error : C4.Error)
  | targetRejected (className : String)
  deriving Repr

/-- One typed data transfer. Removed fields are omitted from this registry;
renaming keeps the payload type, while a conversion can change it. -/
structure FieldTransfer (SourceKey : Type u) (SourceValue : SourceKey → Type v)
    (TargetKey : Type w) (TargetValue : TargetKey → Type x) where
  source : SourceKey
  target : TargetKey
  convert : SourceValue source → Except String (TargetValue target)
  missing : MissingSourcePolicy := .reject

/-- Preserve a value across equal payload types, including a renamed key. -/
def FieldTransfer.preserve {SourceKey : Type u} {SourceValue : SourceKey → Type v}
    {TargetKey : Type w} {TargetValue : TargetKey → Type v}
    (source : SourceKey) (target : TargetKey)
    (same : SourceValue source = TargetValue target)
    (missing : MissingSourcePolicy := .reject) :
    FieldTransfer SourceKey SourceValue TargetKey TargetValue :=
  { source, target, convert := fun value => .ok (cast same value), missing }

/-- Read only the declared source. Missing values either fail or leave the
new class's default/optional policy in control; converters can reject data. -/
def FieldTransfer.evaluate {SourceKey : Type u} {SourceValue : SourceKey → Type v}
    {TargetKey : Type w} {TargetValue : TargetKey → Type x}
    (transfer : FieldTransfer SourceKey SourceValue TargetKey TargetValue)
    (self : Self SourceKey SourceValue) :
    Except (MigrationError SourceKey TargetKey) (Option (TargetValue transfer.target)) :=
  match self transfer.source with
  | none => match transfer.missing with
    | .reject => .error (.missingSource transfer.source)
    | .useTargetDefault => .ok none
  | some value =>
    (transfer.convert value).mapError
      (.conversionFailed transfer.source transfer.target) |>.map some

/-- Renaming a present field preserves its payload through the supplied type
equality; no default or converter inference participates in this operation. -/
theorem FieldTransfer.evaluate_preserve {SourceKey : Type u}
    {SourceValue : SourceKey → Type v} {TargetKey : Type w} {TargetValue : TargetKey → Type v}
    (source : SourceKey) (target : TargetKey) (same : SourceValue source = TargetValue target)
    (missing : MissingSourcePolicy) (self : Self SourceKey SourceValue)
    (value : SourceValue source) (present : self source = some value) :
    (FieldTransfer.preserve source target same missing).evaluate self =
      .ok (some (cast same value)) := by
  simp [FieldTransfer.preserve, FieldTransfer.evaluate, present, Except.map, Except.mapError]

/-- A successful migration carries the new class's runtime acceptance proof. -/
structure Migrated {TargetKey : Type w} {TargetValue : TargetKey → Type x}
    [DecidableEq TargetKey] [BEq TargetKey] [LawfulBEq TargetKey] [Hashable TargetKey]
    (targetClass : ClassSpec TargetKey TargetValue) where
  object : Memoized TargetKey TargetValue
  accepted : targetClass.acceptsObject object = true

private def checkTargets {SourceKey : Type u} {SourceValue : SourceKey → Type v}
    {TargetKey : Type w} {TargetValue : TargetKey → Type x}
    [DecidableEq TargetKey] [BEq TargetKey] [LawfulBEq TargetKey] [Hashable TargetKey]
    (rules : List (SlotRule TargetKey TargetValue))
    (seen : Std.HashSet TargetKey) :
    List (FieldTransfer SourceKey SourceValue TargetKey TargetValue) →
      Except (MigrationError SourceKey TargetKey) Unit
  | [] => .ok ()
  | transfer :: rest => do
    if seen.contains transfer.target then throw (.duplicateTarget transfer.target)
    let some rule := rules.find? (fun rule => decide (rule.key = transfer.target)) |
      throw (.unknownTarget transfer.target)
    if rule.fixed || rule.compute.isSome then throw (.nonDataTarget transfer.target)
    checkTargets rules (seen.insert transfer.target) rest

private def readTransfers {SourceKey : Type u} {SourceValue : SourceKey → Type v}
    {TargetKey : Type w} {TargetValue : TargetKey → Type x}
    [DecidableEq TargetKey] (self : Self SourceKey SourceValue)
    (values : Declaration TargetKey TargetValue) :
    List (FieldTransfer SourceKey SourceValue TargetKey TargetValue) →
      Except (MigrationError SourceKey TargetKey) (Declaration TargetKey TargetValue)
  | [] => .ok values
  | transfer :: rest =>
    match transfer.evaluate self with
    | .error error => .error error
    | .ok value =>
      let next := match value with
        | none => values
        | some value => values.withValue transfer.target value
      readTransfers self next rest

/-- Migrate explicit data into a fresh instance of the new class. Validate
the complete transfer shape before forcing source values. Fixed and computed
target fields come from the target specification, never from a copied target.
The old object remains a readable snapshot; omitted source fields are dropped
from the new object. There is no implicit same-name copying. -/
def ClassSpec.migrateFrom {SourceKey : Type u} {SourceValue : SourceKey → Type v}
    {TargetKey : Type w} {TargetValue : TargetKey → Type x}
    [BEq SourceKey] [LawfulBEq SourceKey] [Hashable SourceKey]
    [DecidableEq TargetKey] [BEq TargetKey] [LawfulBEq TargetKey] [Hashable TargetKey]
    (targetClass : ClassSpec TargetKey TargetValue) (instanceName : String)
    (source : Memoized SourceKey SourceValue)
    (transfers : List (FieldTransfer SourceKey SourceValue TargetKey TargetValue)) :
    Except (MigrationError SourceKey TargetKey) (Migrated targetClass) :=
  match checkTargets targetClass.effectiveRules {} transfers with
  | .error error => .error error
  | .ok () => do
    if instanceName == targetClass.name then throw (.graph (.duplicateNode instanceName))
    let values ← readTransfers source.read .empty transfers
    let base ← targetClass.instantiate.mapError .graph
    let target ← ((base.plan.memoizeUsing source.mode).extend instanceName values).mapError .graph
    if accepted : targetClass.acceptsObject target = true then
      return ⟨target, accepted⟩
    else
      throw (.targetRejected targetClass.name)

end LeanPoo.Object
