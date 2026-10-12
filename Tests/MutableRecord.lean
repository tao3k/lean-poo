import LeanPoo.Prototype.MutableRecordSemantics

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.MutableRecord
namespace LeanPoo.Tests.MutableRecord

private def base : Storage := fromValues [("x", .integer 1), ("y", .integer 2)]
private def x3 : Specification := .slot "x" (constant (.integer 3))
private def doubleX : Specification := .slot "x" (modify fun value => match value with
  | .integer n => .integer (n * 2)
  | _ => value)
private def zFromSelf : Specification := .slot "z" (compute fun self =>
  (self "x").bind fun x => (self "y").map fun y => .list [x, y])
private def mixed := Specification.compose zFromSelf (.compose doubleX x3)

private def pureStorage : Storage := (mixed.transition base).1
#guard readPure pureStorage 3 "x" == .value (.integer 6)
#guard readPure pureStorage 3 "z" == .value (.list [.integer 6, .integer 2])
#guard readPure pureStorage 3 "missing" == .error "missing slot: missing"

private def compare (left right : Storage) (keys : List String) : Bool :=
  keys.all fun key => readPure left 20 key == readPure right 20 key

private def run : IO Unit := do
  let object ← IO.ofExcept (← instantiate mixed base)
  let alias := object
  let before ← object.snapshot
  unless compare before pureStorage ["x", "y", "z", "missing"] do
    throw (IO.userError "mutable mix differs from pure state threading")
  unless (← object.read 3 "z") == .value (.list [.integer 6, .integer 2]) do
    throw (IO.userError "mutable final-self composition")
  object.slot "x" (constant (.integer 10))
  unless (← alias.read 3 "z") == .value (.list [.integer 10, .integer 2]) &&
      readPure before 3 "z" == .value (.list [.integer 6, .integer 2]) do
    throw (IO.userError "same identity or persistent snapshot")
  -- Override skips a captured error and all recursive requests inside it.
  object.slot "x" (fun _ _ => .error "must stay hidden")
  object.slot "x" (constant (.integer 42))
  unless (← alias.read 1 "x") == .value (.integer 42) do
    throw (IO.userError "override forced inherited error")
  -- Failure retains earlier parent writes and refuses later child writes.
  let failed : Specification := .compose (.slot "never" (constant .unit))
    (.compose (.error "stop") (.slot "written" (constant (.boolean true))))
  let failure ← failed.apply object
  unless failure.toOption.isNone && (← object.read 1 "written") == .value (.boolean true) &&
      (← object.read 1 "never") == .error "missing slot: never" do
    throw (IO.userError "partial-state failure ordering")
  let frozen ← object.snapshot
  let clone ← create frozen
  clone.slot "x" (constant (.integer 9))
  unless (← object.read 1 "x") == .value (.integer 42) &&
      (← clone.read 1 "x") == .value (.integer 9) do
    throw (IO.userError "fix! reused base identity")
  -- Automated pure/mutable/linear conversions preserve observable slot values.
  let linear ← LinearState.create base
  let next ← IO.ofExcept (← mixed.applyLinear linear)
  let linearSnapshot ← IO.ofExcept (← next.read)
  unless compare linearSnapshot pureStorage ["x", "y", "z", "missing"] &&
      (← linear.read).toOption.isNone do
    throw (IO.userError "linear conversion or reference consumption")
  let failedState ← LinearState.create base
  let partialAlias := failedState
  let refused ← failed.applyLinear failedState
  let retained ← IO.ofExcept (← partialAlias.read)
  unless !refused.isOk && readPure retained 1 "written" == .value (.boolean true) &&
      readPure retained 1 "never" == .error "missing slot: never" do
    throw (IO.userError "failed linear conversion lost partial writes")
  let resumed ← IO.ofExcept (← x3.applyLinear failedState)
  unless !(← partialAlias.read).isOk &&
      readPure (← IO.ofExcept (← resumed.read)) 1 "written" == .value (.boolean true) do
    throw (IO.userError "linear continuation after partial failure")
  -- Mutual references remain explicit pending observations at a finite budget.
  object.slot "a" (compute fun self => self "b")
  object.slot "b" (compute fun self => self "a")
  unless (← object.read 50 "a") == .pending do
    throw (IO.userError "recursive mutable slot confused pending and error")
  IO.println "POOF-MUTABLE-RECORD-OK sameIdentity=true inheritedLazy=true finalSelf=true pure+linearConversion=true partialErrors=true"
#eval run
#print axioms Specification.compose_assoc
#print axioms write_pureSlot
#print axioms read_returns_iff
#print axioms interpret_sound
#print axioms interpret_complete
#print axioms interpret_projection
#print axioms snapshot_projection
#print axioms linear_failure_observation
end LeanPoo.Tests.MutableRecord
