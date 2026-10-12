import LeanPoo.Prototype.MutableRecordSemantics

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.MutableRecord
namespace LeanPoo.Tests.MutableRecordSemantics

private def primitives : List Specification :=
  [.identity, .error "first", .error "second",
    .slot "x" (constant (.integer 7)),
    .slot "x" (modify fun value => match value with | .integer n => .integer (n+1) | _ => value),
    .slot "z" (compute fun self => (self "x").map id),
    .slot "unused" (constant .unit)]

private def programs : List Specification := primitives ++
  primitives.flatMap (fun child => primitives.map (.compose child ·)) ++
  primitives.flatMap (fun layer =>
    [.compose layer (.compose (.error "stop") (.slot "x" (constant (.integer 11)))),
     .compose (.compose layer (.error "stop")) (.slot "x" (constant (.integer 11))),
     .compose (.slot "x" (constant (.integer 11))) (.compose (.error "stop") layer)])

private def compare (left right : Storage) : Bool :=
  [0,1,4,7].all fun depth => ["x","z","unused","missing"].all fun key =>
    readPure left depth key == readPure right depth key

private def sameStatus : Except String Unit → Except String Unit → Bool
  | .ok _, .ok _ => true
  | .error left, .error right => left == right
  | _, _ => false

private def run : IO Unit := do
  let mut failures := 0
  let mut cases := 0
  for seed in List.range 8 do
    let initial := fromValues [("x", .integer (Int.ofNat seed))]
    for specification in programs do
      let (expected, status) := specification.transition initial
      let object ← create initial
      let alias := object
      let frozen ← object.snapshot
      let observed ← specification.apply object
      unless sameStatus observed status && compare (← alias.snapshot) expected && compare frozen initial do
        throw (IO.userError "mutable partial outcome/alias/snapshot differs from pure protocol")
      let state ← LinearState.create initial
      let oldAlias := state
      let linear ← specification.applyLinear state
      match linear, status with
      | .ok next, .ok _ =>
        unless !(← oldAlias.read).isOk && compare (← IO.ofExcept (← next.read)) expected do
          throw (IO.userError "successful linear state or consumption differs")
      | .error actual, .error wanted =>
        unless actual == wanted && compare (← IO.ofExcept (← oldAlias.read)) expected do
          throw (IO.userError "failed linear state lost writes or first error")
        failures := failures+1
        let next ← IO.ofExcept (← (Specification.slot "continued" (constant .unit)).applyLinear state)
        unless !(← oldAlias.read).isOk &&
            readPure (← IO.ofExcept (← next.read)) 1 "continued" == .value .unit do
          throw (IO.userError "cannot continue retained linear failure")
      | _, _ => throw (IO.userError "linear status differs from pure protocol")
      cases := cases+1
  IO.println s!"POOF-MUTABLE-SEMANTICS-OK cases={cases} failures={failures} keys=4 depths=4 partialWrites=retained firstError=true aliases=true resume=true"

#eval run
#print axioms executes_iff
#print axioms executes_unique
#print axioms interpret_projection
#print axioms snapshot_observation
#print axioms linear_success
#print axioms linear_failure
#print axioms parent_failure_skips_child
#print axioms snapshot_generation_mono
#print axioms snapshot_unchanged_of_generation_eq
end LeanPoo.Tests.MutableRecordSemantics
