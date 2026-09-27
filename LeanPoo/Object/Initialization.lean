import LeanPoo.Object.Class

/-!
POOF section 9 class initialization in Lean: a class retains its typed
descriptor and validated C4 prototype. Constructing an instance contributes
direct values as a child of the class prototype, then validates required and
constrained fields against the class descriptor.
-/

namespace LeanPoo.Object

universe u v

/-- A class descriptor paired with the C4 prototype that supplies instance
initializers. The plan retains the class ancestry, including inherited rules. -/
structure ClassLineage (Key : Type u) (Value : Key → Type v) where
  spec : ClassSpec Key Value
  plan : Plan Key Value

/-- The class is the first C4 node; each rule contributes only its own direct
initializer or default to that node. -/
def ClassLineage.root {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (spec : ClassSpec Key Value) :
    Except C4.Error (ClassLineage Key Value) := do
  let empty : Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let plan ← LeanPoo.mix empty spec.name [] spec.toDeclaration
  return ⟨spec, plan⟩

/-- A subclass adds only its own rules to C4. The descriptor retains the
inherited field shape, with child replacements at their original positions. -/
def ClassLineage.extend {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (parent : ClassLineage Key Value) (name : String)
    (rules : List (SlotRule Key Value))
    (sealed : Bool := parent.spec.sealed) :
    Except C4.Error (ClassLineage Key Value) := do
  let direct : ClassSpec Key Value := { name, rules, sealed }
  let plan ← LeanPoo.extend parent.plan.schema name parent.spec.name
    direct.toDeclaration
  return ⟨parent.spec.derive name rules sealed, plan⟩

/-- The retained class descriptor is the typed equivalent of the paper's
instance-to-class link. The object stores the class C4 lineage plus the
constructor's direct values. -/
structure ClassInstance (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  classSpec : ClassSpec Key Value
  object : Memoized Key Value

inductive ConstructError where
  | c4 (error : C4.Error)
  | rejected (className : String)
  deriving Repr

/-- Constructor values override class initializers on the final instance.
Required fields without an initializer must be supplied by the caller. -/
def ClassLineage.construct {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (lineage : ClassLineage Key Value) (name : String)
    (values : Declaration Key Value) :
    Except ConstructError (ClassInstance Key Value) := do
  let plan ← (LeanPoo.extend lineage.plan.schema name lineage.spec.name values).mapError
    ConstructError.c4
  let object := plan.memoize
  if lineage.spec.acceptsObject object then
    return ⟨lineage.spec, object⟩
  else
    throw (.rejected lineage.spec.name)

end LeanPoo.Object
