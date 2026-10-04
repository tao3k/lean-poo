import LeanPoo.Prototype.Target
import LeanPoo.Object.Prototype
import LeanPoo.Object.Definition

namespace LeanPoo.Tests.TargetPolicies

abbrev Value (_ : String) := Nat
abbrev Self := Object.Self String Value

private def setX (value : Nat) : Prototype.DelayedProto Self Self Self :=
  fun _ inherited => fun key =>
    if key == "x" then some value else inherited.get key

private def changeX (current : Self) : Self :=
  fun key => if key == "x" then some 100 else current key

/-- Extension executes the retained prototype, not the edited target. The
constant replacement instead retains old resolved values after extension. -/
private unsafe def results : Except String (List (Option Nat) × Bool) := do
  let source ← (Object.define (Key := String) (Value := Value) "Formulas" do
    Object.Declaration.Builder.value "x" 1
    Object.Declaration.Builder.slot "double"
      (.self fun self => (self "x").map (2 * ·)))
    |>.mapError (fun _ => "source")
  let pair := source.toFirstClassObject
  let rejected := match pair.updateTarget changeX with
    | .error .forbidden => true
    | _ => false
  let outOfSync := pair.updateTargetOutOfSync changeX
  let frozen := pair.overwriteTargetSpecification changeX
  let detached := pair.detachTarget changeX
  let ordinaryChild := pair.extend (setX 7)
  let outOfSyncChild := outOfSync.extend (setX 7)
  let frozenChild := frozen.extend (setX 7)
  return ([pair.value "x", pair.value "double",
    outOfSync.value "x", outOfSync.value "double",
    frozen.value "x", frozen.value "double",
    detached.get "x", detached.get "double",
    ordinaryChild.value "x", ordinaryChild.value "double",
    outOfSyncChild.value "x", outOfSyncChild.value "double",
    frozenChild.value "x", frozenChild.value "double",
    source.read "x", source.read "double"], rejected)

#eval do
  match results with
  | .ok (values, rejected) =>
    let expected := [some 1, some 2, some 100, some 2,
      some 100, some 2, some 100, some 2, some 7, some 14,
      some 7, some 14, some 7, some 2, some 1, some 2]
    unless values == expected && rejected do
      throw (IO.userError s!"target policy mismatch: {values}, reject={rejected}")
    IO.println "TARGET-POLICIES-OK"
  | .error error => throw (IO.userError error)

end LeanPoo.Tests.TargetPolicies
