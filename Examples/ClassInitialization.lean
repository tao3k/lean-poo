import LeanPoo.Object.Initialization
import LeanPoo.Object.Builder

namespace LeanPoo.Examples.ClassInitialization

inductive Key where
  | width
  | height
  | area
  | color
  | scale
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .width => Nat
  | .height => Nat
  | .area => Nat
  | .scale => Nat
  | .color => String

/-- Width and height have no initializer. Area reads the final instance. -/
def rectangle : Object.ClassSpec Key Value :=
  { name := "Rectangle"
    rules := [
      { key := .width, accepts := fun value => value > 0 },
      { key := .height, accepts := fun value => value > 0 },
      { key := .area
        compute := some (.self fun self =>
          some ((self .width).getD 0 * (self .height).getD 0)) }] }

def coloredRules : List (Object.SlotRule Key Value) :=
  [{ key := .color, default := some "black" }]

/-- A child may replace area without moving it to the end of the class's
field-name order. Its inherited value comes from Rectangle. -/
def scaledRules : List (Object.SlotRule Key Value) :=
  [{ key := .scale, default := some 1 },
   { key := .area
     compute := some (.computed fun self inherited =>
       some ((inherited ()).getD 0 * (self .scale).getD 1)) }]

def lineage : Except C4.Error (Object.ClassLineage Key Value) := do
  let root ← Object.ClassLineage.root rectangle
  let colored ← root.extend "ColoredRectangle" coloredRules
  colored.extend "ScaledColoredRectangle" scaledRules

def constructorValues : Object.Declaration Key Value :=
  Object.Declaration.build do
    Object.Declaration.Builder.value .width 3
    Object.Declaration.Builder.value .height 5

def built : Except Object.ConstructError (Object.ClassInstance Key Value) := do
  let model ← lineage.mapError .c4
  model.construct "rectangle-1" constructorValues

#guard match built with
  | .ok constructed =>
    constructed.classSpec.name == "ScaledColoredRectangle" &&
      constructed.classSpec.fieldNames ==
        [.width, .height, .area, .color, .scale] &&
      constructed.object.plan.precedence ==
        ["rectangle-1", "ScaledColoredRectangle", "ColoredRectangle", "Rectangle"] &&
      constructed.object.read .area == some 15 &&
      constructed.object.read .color == some "black"
  | .error _ => false

/-- Constructor overrides affect a computed field through final self. -/
def overridden : Except Object.ConstructError (Object.ClassInstance Key Value) := do
  let model ← lineage.mapError .c4
  model.construct "rectangle-2" <| Object.Declaration.buildOn constructorValues do
    Object.Declaration.Builder.value .scale 2
    Object.Declaration.Builder.value .color "red"

#guard match overridden with
  | .ok constructed =>
    constructed.object.read .area == some 30 &&
      constructed.object.read .color == some "red"
  | .error _ => false

/-- A constructor may also replace a computed initializer directly. -/
def directArea : Except Object.ConstructError (Object.ClassInstance Key Value) := do
  let model ← lineage.mapError .c4
  model.construct "rectangle-3" <| Object.Declaration.buildOn constructorValues do
    Object.Declaration.Builder.value .area 99

#guard match directArea with
  | .ok constructed => constructed.object.read .area == some 99
  | .error _ => false

/-- A required field with no initializer must be supplied by the caller. -/
def missingHeight : Except Object.ConstructError (Object.ClassInstance Key Value) := do
  let model ← lineage.mapError .c4
  model.construct "missing-height" <| Object.Declaration.build do
    Object.Declaration.Builder.value .width 3

#guard match missingHeight with
  | .error (.rejected "ScaledColoredRectangle") => true
  | _ => false

/-- Field predicates also run after class initialization and overrides. -/
def rejectedWidth : Except Object.ConstructError (Object.ClassInstance Key Value) := do
  let model ← lineage.mapError .c4
  model.construct "zero-width" <| Object.Declaration.buildOn constructorValues do
    Object.Declaration.Builder.value .width 0

#guard match rejectedWidth with
  | .error (.rejected "ScaledColoredRectangle") => true
  | _ => false

end LeanPoo.Examples.ClassInitialization
