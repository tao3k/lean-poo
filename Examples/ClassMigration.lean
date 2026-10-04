import LeanPoo.Object.Migration

namespace LeanPoo.Examples.ClassMigration

inductive V1 where | name
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
inductive V2 where | name | age
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
inductive V3 where | fullName | age | email
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value1 (_ : V1) := String
abbrev Value2 : V2 → Type | .name => String | .age => Nat
abbrev Value3 (_ : V3) := String

private def person1 : Object.ClassSpec V1 Value1 :=
  { name := "Person.v1", sealed := true, rules := [{ key := .name }] }
private def person2 : Object.ClassSpec V2 Value2 :=
  { name := "Person.v2", sealed := true, rules :=
      [{ key := .name }, { key := .age, default := some 0 }] }
private def person3 : Object.ClassSpec V3 Value3 :=
  { name := "Person.v3", sealed := true, rules :=
      [{ key := .fullName }, { key := .age }, { key := .email, default := some "unknown" }] }

private def scenario : Except String (String × Nat × String × String) := do
  let base ← person1.instantiate.mapError (fun _ => "v1 class")
  let first ← (base.extend "Ada.v1"
    (Object.Declaration.empty.withValue .name "Ada")).mapError (fun _ => "v1 data")
  let second ← (person2.migrateFrom "Ada.v2" first
    [Object.FieldTransfer.preserve .name .name rfl]).mapError (fun _ => "v2 migration")
  let edited ← (second.object.reviseDeclaration "Ada.v2" fun declaration =>
    declaration.withValue .age 37).mapError (fun _ => "v2 edit")
  let third ← (person3.migrateFrom "Ada.v3" edited
    [Object.FieldTransfer.preserve .name .fullName rfl,
     { source := .age, target := .age, convert := fun age => .ok (toString age) }])
    |>.mapError (fun _ => "v3 migration")
  return ((third.object.read .fullName).getD "missing",
    (second.object.read .age).getD 999, (third.object.read .age).getD "missing",
    (third.object.read .email).getD "missing")

#guard match scenario with
  | .ok values => values == ("Ada", 0, "37", "unknown")
  | .error _ => false
#eval match scenario with
  | .ok (name, initialAge, convertedAge, email) =>
      s!"Person v1 name={name}; v2 default age={initialAge}; v3 full-name={name}, age={convertedAge}, email={email}"
  | .error message => message

end LeanPoo.Examples.ClassMigration
