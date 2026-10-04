import LeanPoo.Object.Definition
import LeanPoo.Object.Nested

/-! An outer object inherits a slot containing an inner object. Its extension
applies an independent override to that inner object with Gerbil's `.+`
topology. Lean keeps composition failure in the slot's `Except` value. -/

namespace LeanPoo.Examples.NestedObjectDefinition

inductive InnerKey where
  | x
  | z
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev InnerValue (_ : InnerKey) := Nat

inductive OuterKey where
  | component
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev OuterValue (_ : OuterKey) :=
  Except Object.PlusWithError (Object.Memoized InnerKey InnerValue)

def run : Except String (Option Nat × Option Nat) := do
  let innerBase ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "InnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun _ => "invalid inner base")
  let innerOverride ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "InnerOverride" do
    Object.Declaration.Builder.value .x 2).mapError
      (fun _ => "invalid inner override")
  let outerBase ← (Object.define (Key := OuterKey) (Value := OuterValue)
      "OuterBase" do
    Object.Declaration.Builder.value .component (.ok innerBase)).mapError
      (fun _ => "invalid outer base")
  let outerExtension ← (outerBase.extendWith "OuterExtension" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith innerOverride "InnerCombined"))
    |>.mapError (fun _ => "invalid outer extension")
  let result ← (outerExtension.ref .component).mapError
    (fun _ => "missing inner object")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return (inner.read .x, inner.read .z)

#eval run

/-- Two outer branches contribute inner extensions. The outer diamond's C4
order also determines the order in which their inner methods are applied. -/
def diamond : Except String (List String × Option Nat × Option Nat) := do
  let innerBase ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "DiamondInnerBase" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5).mapError
      (fun _ => "invalid inner base")
  let addTen ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "AddTen" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)))
      |>.mapError (fun _ => "invalid additive override")
  let double ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "Double" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)))
      |>.mapError (fun _ => "invalid multiplicative override")
  let outerBase ← (Object.define (Key := OuterKey) (Value := OuterValue)
      "DiamondOuterBase" do
    Object.Declaration.Builder.value .component (.ok innerBase)).mapError
      (fun _ => "invalid outer base")
  let left ← (outerBase.extendWith "Left" do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith addTen "InnerLeft"))
      |>.mapError (fun _ => "invalid left branch")
  let right ← (left.defineWith "Right" ["DiamondOuterBase"] do
    Object.Declaration.Builder.slot .component
      (Object.Nested.plusWith double "InnerRight"))
      |>.mapError (fun _ => "invalid right branch")
  let joined ← (right.defineWith "Diamond" ["Left", "Right"] do
    pure ()) |>.mapError (fun _ => "invalid outer diamond")
  let result ← (joined.ref .component).mapError
    (fun _ => "missing inner object")
  let inner ← result.mapError (fun _ => "invalid inner composition")
  return (joined.plan.precedence, inner.read .x, inner.read .z)

#eval diamond

/-- A nested component's inner C4 graph follows the complete outer graph.
Layout declares no inner method but still carries its inherited order. -/

def liftedWidget : Except String (List String × Option Nat × Option Nat) := do
  let innerBase ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "WidgetDefaults" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5) |>.mapError
      (fun _ => "invalid inner base")
  let trait ← (innerBase.extendWith "WidgetTrait" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 2)))
    |>.mapError (fun _ => "invalid inner trait")
  let basePlan ← Object.compile trait.plan.schema "WidgetDefaults"
    |>.mapError (fun _ => "invalid inner family")
  let outer : Object.Schema OuterKey (fun _ => Nat) :=
    { graph := { nodes :=
        [{ name := "Widget" },
         { name := "Scale", parentOrders := [["Widget"]] },
         { name := "Shift", parentOrders := [["Widget"]] },
         { name := "Layout", parentOrders := [["Scale"]] },
         { name := "Final", parentOrders := [["Shift", "Layout"]] }] }
      declaration := fun _ => none }
  let plan ← Object.compile outer "Final" |>.mapError
    (fun _ => "invalid outer topology")
  let layers ← Object.Nested.Contributions.ofEntries plan
    (Key := InnerKey) (Value := InnerValue) [
      ("Widget", { parentOrders := [["WidgetTrait"]] }),
      ("Scale", { declaration := Object.Declaration.build do
          Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)) }),
      ("Shift", { declaration := Object.Declaration.build do
          Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)) })]
    |>.mapError (fun _ => "invalid inner contributions")
  let inner ← Object.Nested.liftLayersOn plan basePlan.memoize
    "widget" layers.lookup |>.mapError (fun _ => "invalid nested component")
  return (inner.plan.precedence, inner.read .x, inner.read .z)

#eval liftedWidget

/-- Independent component traits use one shared defaults identity. The caller
can constrain their order without duplicating the defaults family. -/
def sharedWidgetTraits : Except String (List String × Option Nat × Option Nat) := do
  let defaults ← (Object.define (Key := InnerKey) (Value := InnerValue)
      "SharedDefaults" do
    Object.Declaration.Builder.value .x 1
    Object.Declaration.Builder.value .z 5) |>.mapError (fun _ => "defaults")
  let shifted ← (defaults.extendWith "ShiftTrait" do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· + 10)))
    |>.mapError (fun _ => "shift trait")
  let family ← (shifted.defineWith "ScaleTrait" ["SharedDefaults"] do
    Object.Declaration.Builder.modifyInherited .x (Option.map (· * 2)))
    |>.mapError (fun _ => "scale trait")
  let outer : Object.Schema OuterKey (fun _ => Nat) :=
    { graph := { nodes := [{ name := "Widget" },
        { name := "Layout", parentOrders := [["Widget"]] }] }
      declaration := fun _ => none }
  let plan ← Object.compile outer "Layout" |>.mapError (fun _ => "layout")
  let layers ← Object.Nested.Contributions.ofEntries plan
    (Key := InnerKey) (Value := InnerValue) [("Widget", {})]
    |>.mapError (fun _ => "component focus")
  let widget ← Object.Nested.liftLayersWithParents plan family
    [["ShiftTrait", "ScaleTrait"]] "shared-widget" layers.lookup
    |>.mapError (fun _ => "component traits")
  return (widget.plan.precedence, widget.read .x, widget.read .z)

#eval sharedWidgetTraits

end LeanPoo.Examples.NestedObjectDefinition
