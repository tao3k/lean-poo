import LeanPoo.Object.Upgrade
import LeanPoo.Object.Migration

/-! Rename class data only after the operation holding the old object returns. -/
namespace LeanPoo.Examples.QuiescentUpgrade
open Object Upgrade

private def before : ClassSpec String (fun _ => String) :=
  { name := "Person.v1", sealed := true, rules := [{ key := "name" }] }
private def after : ClassSpec String (fun _ => String) :=
  { name := "Person.v2", sealed := true, rules :=
      [{ key := "fullName" }, { key := "email", default := some "unknown" },
       { key := "summary", compute := some (.self fun self => do
           return (← self "fullName") ++ "/" ++ (← self "email")) }] }

private def run : IO Unit := do
  let .ok classObject := before.instantiate | throw (IO.userError "initial class")
  let .ok ada := classObject.extend "Ada.v1"
      (Declaration.empty.withValue "name" "Ada") | throw (IO.userError "initial data")
  let runtime ← Runtime.new ada
  let saved ← IO.mkRef (none : Option (Session String (fun _ => String)))
  let migrate := fun old =>
    (after.migrateFrom "Ada.v2" old [FieldTransfer.preserve "name" "fullName" rfl]).map (·.object)
  let .ok old ← runtime.withSnapshot (fun version object => do
      let .ok session ← runtime.pause | throw (IO.userError "pause")
      saved.set (some session)
      let blocked ← session.commit migrate
      unless (match blocked with | .error (.control (.busy 1)) => true | _ => false) do
        throw (IO.userError "upgrade ran inside active operation")
      unless version == 0 && object.read "name" == some "Ada" do
        throw (IO.userError "old operation changed")
      return object) | throw (IO.userError "admission")
  let some session ← saved.get | throw (IO.userError "missing request")
  unless (← session.commit migrate).toOption == some 1 do
    throw (IO.userError "migration after quiescence")
  let result ← runtime.withSnapshot fun version object =>
    pure (version, object.read "name", object.read "summary", after.acceptsObject object)
  unless result.toOption == some (1, none, some "Ada/unknown", true) &&
      old.read "name" == some "Ada" do
    throw (IO.userError "migration snapshot contract")
  IO.println "Person upgrade: busy in v0 operation; drained -> v1 Ada/unknown; old snapshot Ada"

#eval run
end LeanPoo.Examples.QuiescentUpgrade
