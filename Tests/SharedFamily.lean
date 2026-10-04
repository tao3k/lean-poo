import LeanPoo.Object.SharedFamily
import LeanPoo.Object.Definition

namespace LeanPoo.Tests.SharedFamily

abbrev Value (_ : String) := Nat

private def snapshots : Except C4.Error
    (Object.Memoized String Value × Object.Memoized String Value) := do
  let seed ← Object.define (Key := String) (Value := Value) "Seed" do
    Object.Declaration.Builder.value "x" 1
    Object.Declaration.Builder.value "z" 5
  let left ← seed.extendWith "Left" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· + 10))
  let right ← seed.extendWith "Right" do
    Object.Declaration.Builder.modifyInherited "x" (Option.map (· * 2))
  return (left.plan.memoizeCompiled, right.plan.memoizeIndexed)

private def branches : Except String Bool := do
  let (left, right) ← snapshots |>.mapError (fun _ => "snapshots")
  let joined ← left.mixSharedWith right ["Seed"] "Joined"
    |>.mapError (fun _ => "joined")
  let reverse ← right.mixSharedWith left ["Seed"] "Reverse"
    |>.mapError (fun _ => "reverse")
  let repeatedRoot ← left.mixSharedWith left ["Seed", "Left"] "RepeatedRoot"
    |>.mapError (fun _ => "shared root")
  let seed := joined.plan.schema.graph.nodes.filter (·.name == "Seed")
  let some root := joined.plan.schema.graph.findNode? "Joined" | return false
  return joined.plan.precedence == ["Joined", "Left", "Right", "Seed"] &&
    joined.read "x" == some 12 && joined.read "z" == some 5 &&
    joined.mode == .compiled && seed.length == 1 &&
    root.parentOrders == [["Left"], ["Right"]] &&
    reverse.plan.precedence == ["Reverse", "Right", "Left", "Seed"] &&
    reverse.read "x" == some 22 && reverse.mode == .indexed &&
    repeatedRoot.plan.precedence == ["RepeatedRoot", "Left", "Seed"] &&
    repeatedRoot.read "x" == some 11 && left.read "x" == some 11 &&
    right.read "x" == some 2

#guard match branches with
  | .ok true => true
  | _ => false

/-- The API selects declaration authority explicitly. Equal metadata does
not mean equal bodies, and an absent authoritative declaration must not
fall through to the other snapshot's declaration. -/
private def ownership : Except String Bool := do
  let (left, right) ← snapshots |>.mapError (fun _ => "snapshots")
  let different ← right.reviseDeclaration "Seed"
    (fun declaration => declaration.withValue "x" 9)
    |>.mapError (fun _ => "different declaration")
  let joined ← left.mixSharedWith different ["Seed"] "Authority"
    |>.mapError (fun _ => "authority")
  let rightAuthority ← different.mixSharedWith left ["Seed"] "OtherAuthority"
    |>.mapError (fun _ => "right authority")
  let absentSchema : Object.Schema String Value :=
    { left.plan.schema with declaration := fun name =>
        if name == "Seed" then none else left.plan.schema.declaration name }
  let absent ← Object.compile absentSchema "Left" |>.mapError (fun _ => "absent")
  let noFallback ← absent.memoize.mixSharedWith different ["Seed"] "AbsentAuthority"
    |>.mapError (fun _ => "absent authority")
  return joined.read "x" == some 12 && different.read "x" == some 18 &&
    rightAuthority.read "x" == some 38 && noFallback.read "x" == none &&
    noFallback.read "z" == none && left.read "x" == some 11

#guard match ownership with
  | .ok true => true
  | _ => false

private def metadataAndNames : Except C4.Error Bool := do
  let (left, right) ← snapshots
  let unlisted := match left.mixSharedWith right [] "Unlisted" with
    | .error (.merge (.undeclaredCollision "Seed")) => true
    | _ => false
  let unknown := match left.mixSharedWith right ["Missing"] "Unknown" with
    | .error (.merge (.notShared "Missing")) => true
    | _ => false
  let oneSide := match left.mixSharedWith right ["Left"] "OneSide" with
    | .error (.merge (.notShared "Left")) => true
    | _ => false
  let repeated := match left.mixSharedWith right ["Seed", "Seed"] "Repeated" with
    | .error (.merge (.repeatedSharedName "Seed")) => true
    | _ => false
  let duplicate := match left.mixSharedWith right ["Seed"] "Left" with
    | .error (.c4 (.duplicateNode "Left")) => true
    | _ => false
  let suffixed : Object.Schema String Value :=
    { right.plan.schema with graph := { nodes :=
        right.plan.schema.graph.nodes.map (fun node => if node.name == "Seed" then { node with suffix := true } else node) } }
  let suffixConflict := match left.plan.schema.mergeSharedFromLeft suffixed ["Seed"] with
    | .error (.conflictingMetadata "Seed") => true
    | _ => false
  let differentParents : Object.Schema String Value :=
    { right.plan.schema with graph := { nodes :=
        right.plan.schema.graph.nodes.map (fun node =>
          if node.name == "Seed" then { node with parentOrders := [["Other"]] } else node)
        ++ [{ name := "Other" }] } }
  let parentConflict := match left.plan.schema.mergeSharedFromLeft differentParents ["Seed"] with
    | .error (.conflictingMetadata "Seed") => true
    | _ => false
  let duplicated : Object.Schema String Value :=
    { right.plan.schema with graph := { nodes := right.plan.schema.graph.nodes ++ [{ name := "Seed" }] } }
  let malformed := match left.plan.schema.mergeSharedFromLeft duplicated ["Seed"] with
    | .error (.graph (.duplicateNode "Seed")) => true
    | _ => false
  let missingParent : Object.Schema String Value :=
    { right.plan.schema with graph := { nodes :=
        right.plan.schema.graph.nodes.map (fun node =>
          if node.name == "Seed" then { node with parentOrders := [["Missing"]] } else node) } }
  let malformedParent := match left.plan.schema.mergeSharedFromLeft missingParent ["Seed"] with
    | .error (.graph (.unknownNode "Missing")) => true
    | _ => false
  return unlisted && unknown && oneSide && repeated && duplicate &&
    suffixConflict && parentConflict && malformed && malformedParent

#guard match metadataAndNames with
  | .ok true => true
  | _ => false

private def incompatibleOrders : Except C4.Error Bool := do
  let first ← Object.define (Key := String) (Value := Value) "First" do pure ()
  let family ← first.defineWith "Second" [] do pure ()
  let left ← family.defineWith "Left" ["First", "Second"] do pure ()
  let right ← family.defineWith "Right" ["Second", "First"] do pure ()
  return match left.mixSharedWith right ["First", "Second"] "Conflict" with
    | .error (.c4 .inconsistentOrder) => true
    | _ => false

#guard match incompatibleOrders with
  | .ok true => true
  | _ => false

private def nested : Except String Bool := do
  let (left, right) ← snapshots |>.mapError (fun _ => "snapshots")
  let outerValue (_ : String) :=
    Except Object.SharedCombineError (Object.Memoized String Value)
  let outer ← (Object.define (Key := String) (Value := outerValue) "Container" do
    Object.Declaration.Builder.value "component" (.ok left))
    |>.mapError (fun _ => "container")
  let extended ← (outer.extendWith "ContainerExtension" do
    Object.Declaration.Builder.slot "component"
      (Object.Nested.mixSharedWith right ["Seed"] "Inner"))
    |>.mapError (fun _ => "container extension")
  let result ← extended.ref "component" |>.mapError (fun _ => "component")
  let inner ← result |>.mapError (fun _ => "inner")
  let method := Object.Nested.mixSharedWith (Outer := Unit) right ["Seed"] "Missing"
  let absent := (method.eval () (fun _ => none)).isNone
  let earlier := match method.eval () (fun _ => some (.error (.c4 .inconsistentOrder))) with
    | some (.error (.c4 .inconsistentOrder)) => true
    | _ => false
  return inner.read "x" == some 12 && inner.read "z" == some 5 && absent && earlier

#guard match nested with
  | .ok true => true
  | _ => false

end LeanPoo.Tests.SharedFamily
