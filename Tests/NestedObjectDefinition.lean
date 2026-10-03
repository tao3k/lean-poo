import LeanPoo.Object.Definition
import LeanPoo.Object.Nested

namespace LeanPoo.Tests.NestedObjectDefinition

inductive Key where
  | x
  | z
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value (_ : Key) := Nat

private def plusTopology : Except Object.PlusWithError
    (List String × Option Nat × Option Nat × Bool × Bool) := do
  let base ← (Object.define (Key := Key) (Value := Value) "Base" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun error => .composition (.c4 error))
  let parent ← (Object.define (Key := Key) (Value := Value) "Parent" do
    Object.Declaration.Builder.value .z 7).mapError
      (fun error => .composition (.c4 error))
  let override ← (parent.extendWith "Override" do
    Object.Declaration.Builder.value .x 2).mapError
      (fun error => .composition (.c4 error))
  let combined ← base.plan.memoizeCompiled |>.plusWith override "Combined"
  let collision := match base.plusWith base "Repeated" with
    | .error (.schema (.duplicateNode "Base")) => true
    | _ => false
  return (combined.plan.precedence, combined.read .x,
    combined.read .z, combined.mode == .compiled, collision)

#guard match plusTopology with
  | .ok (["Combined", "Parent", "Base"], some 2, some 7,
      true, true) => true
  | _ => false

inductive OuterKey where
  | component
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev OuterValue (_ : OuterKey) :=
  Except Object.PlusWithError (Object.Memoized Key Value)

private def nestedError : Except C4.Error Bool := do
  let inner ← Object.define (Key := Key) (Value := Value) "Inner" do
    Object.Declaration.Builder.value .x 1
  let outer ← Object.define (Key := OuterKey) (Value := OuterValue) "Outer" do
    Object.Declaration.Builder.value .component (.ok inner)
  let revised ← outer.extendWith "Revised" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith inner "Collision")
  return match revised.read .component with
    | some (.error (.schema (.duplicateNode "Inner"))) => true
    | _ => false

#guard match nestedError with
  | .ok true => true
  | _ => false

private def nestedDiamond : Except String
    (List String × Option Nat × Option Nat) := do
  let base ← (Object.define (Key := Key) (Value := Value) "InnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun _ => "invalid inner base")
  let addTen ← (Object.define (Key := Key) (Value := Value) "AddTen" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)))
      |>.mapError (fun _ => "invalid left override")
  let double ← (Object.define (Key := Key) (Value := Value) "Double" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)))
      |>.mapError (fun _ => "invalid right override")
  let outer ← (Object.define (Key := OuterKey) (Value := OuterValue)
      "OuterBase" do
    Object.Declaration.Builder.value .component (.ok base)).mapError
      (fun _ => "invalid outer base")
  let left ← (outer.extendWith "Left" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith addTen "InnerLeft"))
      |>.mapError (fun _ => "invalid left")
  let right ← (left.defineWith "Right" ["OuterBase"] do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith double "InnerRight"))
      |>.mapError (fun _ => "invalid right")
  let diamond ← (right.defineWith "Diamond" ["Left", "Right"] do
    pure ()) |>.mapError (fun _ => "invalid diamond")
  let result ← (diamond.ref .component).mapError
    (fun _ => "missing component")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return (diamond.plan.precedence, inner.read .x, inner.read .z)

#guard match nestedDiamond with
  | .ok (["Diamond", "Left", "Right", "OuterBase"], some 12,
      some 5) => true
  | _ => false

abbrev SharedValue (_ : OuterKey) :=
  Except LeanPoo.CompositionError (Object.Memoized Key Value)

private def nestedSharedFamily : Except String (Option Nat) := do
  let base ← (Object.define (Key := Key) (Value := Value) "SharedBase" do
    Object.Declaration.Builder.value .x 1).mapError
      (fun _ => "invalid base")
  let override ← (base.defineWith "SharedOverride" [] do
    Object.Declaration.Builder.value .x 2).mapError
      (fun _ => "invalid override")
  let basePlan ← (Object.compile override.plan.schema "SharedBase").mapError
    (fun _ => "invalid base plan")
  let outer ← (Object.define (Key := OuterKey) (Value := SharedValue)
      "SharedOuter" do
    Object.Declaration.Builder.value .component (.ok basePlan.memoize))
      |>.mapError (fun _ => "invalid outer")
  let extended ← (outer.extendWith "SharedOuterExtension" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plus "InnerCombined" "SharedOverride"))
      |>.mapError (fun _ => "invalid outer extension")
  let result ← (extended.ref .component).mapError
    (fun _ => "missing component")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return inner.read .x

#guard match nestedSharedFamily with
  | .ok (some 2) => true
  | _ => false

private def liftedContributions : String → Option (Object.Declaration Key Value)
  | "Origin" => some <| Object.Declaration.build do
      Object.Declaration.Builder.value .x 1
      Object.Declaration.Builder.value .z 5
  | "Left" => some <| Object.Declaration.build do
      Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10))
  | "Right" => some <| Object.Declaration.build do
      Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2))
  | _ => none

private def outerTopology : Except C4.Error
    (Object.Plan OuterKey (fun _ => Nat)) :=
  let schema : Object.Schema OuterKey (fun _ => Nat) :=
    { graph := { nodes :=
        [{ name := "Origin" },
         { name := "Left", parentOrders := [["Origin"]] },
         { name := "Right", parentOrders := [["Origin"]] },
         { name := "Bridge", parentOrders := [["Left"]] },
         { name := "Unused" },
         { name := "Diamond", parentOrders :=
             [["Bridge"], ["Right", "Unused"]] }] }
      declaration := fun _ => none }
  Object.compile schema "Diamond"

private def liftedOuterDag : Except Object.Nested.LiftError Bool := do
  let outer ← outerTopology |>.mapError .c4
  let some inner ← Object.Nested.lift outer "focus"
      liftedContributions | return false
  let expected := (outer.precedence.filter (· != "Unused")).map
    (Object.Nested.liftedName "focus")
  let some bridge := inner.plan.schema.graph.findNode? "focus/Bridge" |
    return false
  return inner.plan.precedence == expected &&
    bridge.parentOrders == [["focus/Left"]] &&
    (inner.plan.schema.graph.findNode? "focus/Unused").isNone &&
    inner.read .x == some 12 && inner.read .z == some 5

#guard match liftedOuterDag with
  | .ok true => true
  | _ => false

private def checkedContributions : Except String Bool := do
  let outer ← outerTopology |>.mapError (fun _ => "invalid outer DAG")
  let entries : List (String × Object.Nested.Layer Key Value) :=
    ["Right", "Origin", "Left"].map fun name =>
      (name, { declaration := (liftedContributions name).getD Object.Declaration.empty })
  let layers ← Object.Nested.Contributions.ofEntries outer entries
    |>.mapError (fun _ => "invalid contributors")
  let some inner ← Object.Nested.liftLayers outer "checked" layers.lookup
    |>.mapError (fun _ => "invalid checked lift") | return false
  let duplicate := match Object.Nested.Contributions.ofEntries outer
      (entries ++ [("Right", { declaration := Object.Declaration.empty })]) with
    | .error (.duplicateLayer "Right") => true
    | _ => false
  let unknown := match Object.Nested.Contributions.ofEntries outer
      (entries ++ [("Typo", { declaration := Object.Declaration.empty })]) with
    | .error (.unknownOuterNode "Typo") => true
    | _ => false
  return inner.read .x == some 12 &&
    inner.plan.precedence.take 4 ==
      ["checked/Diamond", "checked/Bridge", "checked/Left", "checked/Right"] &&
    duplicate && unknown

#guard match checkedContributions with
  | .ok true => true
  | _ => false

private def liftedOnBase : Except String Bool := do
  let outer ← outerTopology |>.mapError (fun _ => "invalid outer DAG")
  let base ← (Object.define (Key := Key) (Value := Value) "Stored" do
    Object.Declaration.Builder.value .z 7) |>.mapError
      (fun _ => "invalid inner base")
  let lifted ← Object.Nested.liftOn outer base.plan.memoizeCompiled
    "focus" (fun name =>
      if name == "Origin" then
        some <| Object.Declaration.build do
          Object.Declaration.Builder.value .x 1
      else liftedContributions name)
    |>.mapError (fun _ => "invalid nested lift")
  let expected := (outer.precedence.filter (· != "Unused")).map
    (Object.Nested.liftedName "focus") ++ ["Stored"]
  return lifted.plan.precedence == expected &&
    lifted.read .x == some 12 && lifted.read .z == some 7 &&
    lifted.mode == .compiled

#guard match liftedOnBase with
  | .ok true => true
  | _ => false

private def liftedCollision : Except C4.Error Bool := do
  let outer ← outerTopology
  let base ← Object.define (Key := Key) (Value := Value)
    "focus/Origin" do pure ()
  return match Object.Nested.liftOn outer base "focus"
      liftedContributions with
    | .error (.schema (.duplicateNode "focus/Origin")) => true
    | _ => false

#guard match liftedCollision with
  | .ok true => true
  | _ => false

private def absentFocus : Except String Bool := do
  let outer ← outerTopology |>.mapError (fun _ => "invalid outer DAG")
  let noContribution : String → Option (Object.Declaration Key Value) :=
    fun _ => none
  let lifted ← Object.Nested.lift outer "empty" noContribution
    |>.mapError (fun _ => "invalid empty focus")
  let base ← (Object.define (Key := Key) (Value := Value) "Unchanged" do
    Object.Declaration.Builder.value .x 9) |>.mapError
      (fun _ => "invalid base")
  let derived ← Object.Nested.liftOn outer base "empty" noContribution
    |>.mapError (fun _ => "invalid base focus")
  return lifted.isNone && derived.plan.precedence == ["Unchanged"] &&
    derived.read .x == some 9

#guard match absentFocus with
  | .ok true => true
  | _ => false

private def liftedSuffix : Except Object.Nested.LiftError Bool := do
  let schema : Object.Schema OuterKey (fun _ => Nat) :=
    { graph := { nodes :=
        [{ name := "Base", suffix := true },
         { name := "Child", parentOrders := [["Base"]], suffix := true }] }
      declaration := fun _ => none }
  let outer ← Object.compile schema "Child" |>.mapError .c4
  let contribution : String → Option (Object.Declaration Key Value)
    | "Base" => some <| Object.Declaration.empty.withValue .x 4
    | _ => none
  let some inner ← Object.Nested.lift outer "suffix" contribution |
    return false
  let some child := inner.plan.schema.graph.findNode? "suffix/Child" |
    return false
  let layer : String → Option (Object.Nested.Layer Key Value)
    | "Base" => some {
        declaration := Object.Declaration.empty.withValue .x 4 }
    | "Child" => some { suffix := some false }
    | _ => none
  let some changed ← Object.Nested.liftLayers outer "custom" layer |
    return false
  let some revised := changed.plan.schema.graph.findNode? "custom/Child" |
    return false
  return child.suffix && inner.plan.precedence ==
    ["suffix/Child", "suffix/Base"] && inner.read .x == some 4 &&
    !revised.suffix && changed.read .x == some 4

#guard match liftedSuffix with
  | .ok true => true
  | _ => false

private def independentInnerParent : Except String Bool := do
  let outer ← outerTopology |>.mapError (fun _ => "invalid outer DAG")
  let base ← (Object.define (Key := Key) (Value := Value) "InnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5) |>.mapError
      (fun _ => "invalid inner base")
  let trait ← (base.extendWith "InnerTrait" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 2)))
    |>.mapError (fun _ => "invalid independent inner parent")
  let basePlan ← Object.compile trait.plan.schema "InnerBase"
    |>.mapError (fun _ => "invalid inner family")
  let layers : String → Option (Object.Nested.Layer Key Value)
    | "Origin" => some { parentOrders := [["InnerTrait"]] }
    | name => (liftedContributions name).map fun declaration =>
        { declaration }
  let inner ← Object.Nested.liftLayersOn outer basePlan.memoize
    "layer" layers |>.mapError (fun _ => "invalid layered lift")
  let some origin := inner.plan.schema.graph.findNode? "layer/Origin" |
    return false
  return origin.parentOrders == [["InnerTrait"], ["InnerBase"]] &&
    inner.read .x == some 16 && inner.read .z == some 5 &&
    inner.plan.precedence.contains "InnerTrait"

#guard match independentInnerParent with
  | .ok true => true
  | _ => false

private def multipleInnerFamilies : Except String Bool := do
  let outer ← outerTopology |>.mapError (fun _ => "invalid outer DAG")
  let valueBase ← (Object.define (Key := Key) (Value := Value) "ValueBase" do
    Object.Declaration.Builder.value .x 1) |>.mapError
      (fun _ => "invalid value base")
  let metadataBase ← (Object.define (Key := Key) (Value := Value)
    "MetadataBase" do
      Object.Declaration.Builder.value .z 5) |>.mapError
        (fun _ => "invalid metadata base")
  let layers : String → Option (Object.Nested.Layer Key Value)
    | "Left" => some { declaration := Object.Declaration.build do
        Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)) }
    | "Right" => some { declaration := Object.Declaration.build do
        Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)) }
    | _ => none
  let inner ← Object.Nested.liftLayersOnMany outer
    valueBase.plan.memoizeCompiled [metadataBase] "many" layers
      |>.mapError (fun _ => "invalid multiple-family lift")
  let collision := match Object.Nested.liftLayersOnMany outer
      valueBase [valueBase] "collision" layers with
    | .error (.schema (.duplicateNode "ValueBase")) => true
    | _ => false
  let missing := match Object.Nested.liftLayersOnMany outer
      valueBase [metadataBase] "empty" (fun _ => none) with
    | .error .missingFocus => true
    | _ => false
  return inner.read .x == some 12 && inner.read .z == some 5 &&
    inner.mode == .compiled &&
    inner.plan.precedence.contains "ValueBase" &&
    inner.plan.precedence.contains "MetadataBase" && collision && missing

#guard match multipleInnerFamilies with
  | .ok true => true
  | _ => false

/-- Two inner roots share one seed. Noncommuting methods expose parent order,
and the seed must occur once even when several outer leaves inherit it. -/
private def commonInnerFamily : Except String Bool := do
  let seed ← (Object.define (Key := Key) (Value := Value) "Seed" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5) |>.mapError (fun _ => "seed")
  let left ← (seed.extendWith "Add" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)))
    |>.mapError (fun _ => "add")
  let family ← (left.defineWith "Double" ["Seed"] do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)))
    |>.mapError (fun _ => "double")
  let outer ← Object.compile
    ({ graph := { nodes := [{ name := "Component" }] }
       declaration := fun _ => none } : Object.Schema OuterKey OuterValue)
    "Component" |>.mapError (fun _ => "outer")
  let layer : String → Option (Object.Nested.Layer Key Value) :=
    fun _ => some {}
  let forward ← Object.Nested.liftLayersWithParents outer
    family.plan.memoizeCompiled [["Add", "Double"]] "forward" layer
    |>.mapError (fun _ => "forward")
  let reverse ← Object.Nested.liftLayersWithParents outer
    family.plan.memoizeIndexed [["Double", "Add"]] "reverse" layer
    |>.mapError (fun _ => "reverse")
  let independent ← Object.Nested.liftLayersWithParents outer family
    [["Add"], ["Double"]] "independent" layer
    |>.mapError (fun _ => "independent")
  let some independentRoot := independent.plan.schema.graph.findNode?
      "independent/Component" | return false
  let orderedFamily ← (family.defineWith "Ordered" ["Add", "Double"] do
    pure ()) |>.mapError (fun _ => "ordered family")
  let reordered ← Object.Nested.liftLayersWithParents outer orderedFamily
    [["Double"], ["Ordered"]] "reordered" layer
    |>.mapError (fun _ => "independent reordering")
  let forcedConflict := match Object.Nested.liftLayersWithParents outer
      orderedFamily [["Double", "Ordered"]] "forced" layer with
    | .error (.c4 .inconsistentOrder) => true
    | _ => false
  let diamond ← outerTopology |>.mapError (fun _ => "diamond")
  let branches : String → Option (Object.Nested.Layer Key Value)
    | "Left" => some {}
    | "Right" => some {}
    | _ => none
  let shared ← Object.Nested.liftLayersWithParents diamond family
    [["Add", "Double"]] "shared" branches
    |>.mapError (fun _ => "shared leaves")
  let unknown := match Object.Nested.liftLayersWithParents outer family
      [["absent"]] "unknown" layer with
    | .error (.c4 (.unknownNode "absent")) => true
    | _ => false
  let liftedReference := match Object.Nested.liftLayersWithParents outer family
      [["self/Component"]] "self" layer with
    | .error (.c4 (.unknownNode "self/Component")) => true
    | _ => false
  let conflict := match Object.Nested.liftLayersWithParents outer family
      [["Add", "Double"], ["Double", "Add"]] "conflict" layer with
    | .error (.c4 .inconsistentOrder) => true
    | _ => false
  let empty := match Object.Nested.liftLayersWithParents outer family
      [["Add", "Double"]] "empty" (fun _ => none) with
    | .error .missingFocus => true
    | _ => false
  let collisionFamily ← (family.defineWith "collision/Component" [] do
    pure ()) |>.mapError (fun _ => "collision family")
  let collision := match Object.Nested.liftLayersWithParents outer
      collisionFamily [["Add", "Double"]] "collision" layer with
    | .error (.schema (.duplicateNode "collision/Component")) => true
    | _ => false
  return forward.plan.precedence ==
      ["forward/Component", "Add", "Double", "Seed"] &&
    reverse.plan.precedence ==
      ["reverse/Component", "Double", "Add", "Seed"] &&
    forward.read .x == some 12 && reverse.read .x == some 22 &&
    forward.read .z == some 5 && forward.mode == .compiled &&
    reverse.mode == .indexed &&
    independentRoot.parentOrders == [["Add"], ["Double"]] &&
    (shared.plan.precedence.filter (· == "Seed")).length == 1 &&
    shared.read .x == some 12 && family.read .x == some 2 &&
    family.plan.precedence == ["Double", "Seed"] &&
    reordered.plan.precedence ==
      ["reordered/Component", "Ordered", "Add", "Double", "Seed"] &&
    reordered.read .x == some 12 && forcedConflict &&
    unknown && liftedReference && conflict && empty && collision

#guard match commonInnerFamily with
  | .ok true => true
  | _ => false

private def unknownInnerParent : Except C4.Error Bool := do
  let outer ← outerTopology
  let base ← Object.define (Key := Key) (Value := Value)
    "KnownBase" do pure ()
  let layers : String → Option (Object.Nested.Layer Key Value)
    | "Origin" => some { parentOrders := [["MissingInnerParent"]] }
    | _ => none
  return match Object.Nested.liftLayersOn outer base "invalid" layers with
    | .error (.c4 (.unknownNode "MissingInnerParent")) => true
    | _ => false

#guard match unknownInnerParent with
  | .ok true => true
  | _ => false

end LeanPoo.Tests.NestedObjectDefinition
