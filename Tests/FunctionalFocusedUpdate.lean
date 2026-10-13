import LeanPoo.Functional.FocusedUpdate
import LeanPoo.Functional.Codec
import LeanPoo.Functional.StatefulValidation

namespace LeanPoo.Tests.FunctionalFocusedUpdate
open Functional Prototype
abbrev Whole := ((Nat → Nat) × Nat) × String
def outer : Focus Whole ((Nat → Nat) × Nat) :=
  ⟨Prod.fst, fun value whole => (value, whole.2), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def inner : Focus ((Nat → Nat) × Nat) (Nat → Nat) :=
  ⟨Prod.fst, fun value whole => (value, whole.2), fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
def method := outer.compose inner
def stock : Focus Whole Nat :=
  ⟨fun whole => whole.1.2, fun value whole => ((whole.1.1, value), whole.2),
    fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
theorem independent : Focus.Independent method stock := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

-- Coefficients/intercepts are an independent affine model; only actual outputs
-- are sampled through the function-valued production representation.
#eval do
  let mut cases := 0
  for coefficient in List.range 4 do
    for intercept in List.range 3 do
      for quantity in List.range 5 do
        for fee in [0,1,3] do
          for factor in [0,2,4] do
            let source : Whole := ((fun q => coefficient*q+intercept, 7), "outside")
            let parent (self : Nat) (old : Nat → Nat) := fun q => old q + self
            let child (_ : Nat) (old : Nat → Nat) := fun q => old q * factor
            let actual := DelayedProto.compose (method.prototype child) (method.prototype parent)
              (Thunk.pure fee) (Thunk.pure source)
            let reverse := DelayedProto.compose (method.prototype parent) (method.prototype child)
              (Thunk.pure fee) (Thunk.pure source)
            let flattened := (outer.compose inner).modify (fun old q => (old q+fee)*factor) source
            let successive := outer.modify (inner.modify (fun old q => (old q+fee)*factor)) source
            let left := stock.modify (·+2) actual
            let right := method.modify (fun old q => (old q+fee)*factor) (stock.modify (·+2) source)
            unless actual.1.1 quantity == (coefficient*quantity+intercept+fee)*factor &&
                reverse.1.1 quantity == (coefficient*quantity+intercept)*factor+fee &&
                flattened.1.1 quantity == actual.1.1 quantity && successive.1.1 quantity == actual.1.1 quantity &&
                actual.1.2 == 7 && actual.2 == "outside" && left.1.2 == 9 &&
                left.1.1 quantity == right.1.1 quantity && left.2 == right.2 do
              throw (IO.userError "nested wrapping/order/frame differs from affine control")
            cases := cases+1
  unless cases == 540 do throw (IO.userError s!"focused coverage drift: {cases}")
  IO.println s!"FUNCTIONAL-FOCUSED-WRAPPERS-OK cases={cases}"

abbrev Wire := Bool × Nat
def input := (Codec.identity Bool String).product
  ((Codec.identity Nat String).refine (fun amount => 0 < amount ∧ amount ≤ 4) "input")
def step (fee ceiling : Nat) (source : Whole) (wire : Wire) : Except String (Nat × Nat) × Whole :=
  match input.decode wire with
  | .error error => (.error error, source)
  | .ok command =>
    let (outcome, next) := method.checkedWith
      (Approved := {price : Nat → Nat // price source.1.2 ≤ ceiling}) Subtype.val (fun old =>
      let price := if command.1 then (fun q => old q+fee*command.2.val) else (fun q => old q*command.2.val)
      if admitted : price source.1.2 ≤ ceiling then .ok ⟨price, admitted⟩ else .error "output") source
    (outcome.map (fun approved => (approved.val 0, approved.val source.1.2)), next)

private def control (fee ceiling maximum : Nat) (state : Nat × Nat) :
    List Wire → Except String (List (Nat × Nat)) × (Nat × Nat)
  | [] => (.ok [], state)
  | (add, amount) :: rest =>
    if amount == 0 || amount > 4 then (.error "input", state) else
      let next := if add then (state.1, state.2+fee*amount) else (state.1*amount, state.2*amount)
      if next.1*maximum+next.2 > ceiling then (.error "output", state) else
        let (outcome, final) := control fee ceiling maximum next rest
        (outcome.map ((next.2, next.1*maximum+next.2) :: ·), final)

private def equal : Except String (List (Nat × Nat)) → Except String (List (Nat × Nat)) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

#eval do
  let mut cases := 0
  let mut resumed := 0
  for coefficient in List.range 3 do
    for fee in List.range 3 do
      for ceiling in [0,4,12,30] do
        for maximum in [0,2,4] do
          for commands in [[],[(true,1)],[(false,2),(true,1)],[(true,1),(false,3),(true,4)],
              [(true,1),(false,0),(true,2)],[(false,5)],[(true,4),(false,4),(true,1)]] do
            let wires : List Wire := commands
            let source : Whole := ((fun q => coefficient*q+1, maximum), "outside")
            let actual := Validation.traverseState (step fee ceiling) source wires
            let expected := control fee ceiling maximum (coefficient,1) wires
            unless equal actual.1 expected.1 && actual.2.1.2 == maximum && actual.2.2 == "outside" do
              throw (IO.userError "focused checked batch outcome or frame differs")
            for quantity in List.range 6 do
              unless actual.2.1.1 quantity == expected.2.1*quantity+expected.2.2 do
                throw (IO.userError "refusal retained the wrong pricing function")
            let continued := Validation.traverseState (step fee ceiling) actual.2 [(true,1)]
            let nextControl := control fee ceiling maximum expected.2 [(true,1)]
            unless equal continued.1 nextControl.1 && continued.2.1.1 5 == nextControl.2.1*5+nextControl.2.2 do
              throw (IO.userError "resumed focus lost accumulated state")
            resumed := resumed+1
            cases := cases+1
  unless cases == 756 && resumed == 756 do throw (IO.userError s!"checked focus coverage drift: {cases}/{resumed}")
  IO.println s!"FUNCTIONAL-FOCUSED-BATCH-OK cases={cases} resumed={resumed}"

private partial def unreachable (source : Whole) : Except String (Nat × Nat) × Whole := unreachable source
private def guarded (source : Whole) (wire : Wire) :=
  if wire.2 == 999 then unreachable source else step 2 0 source wire
#eval do
  let source : Whole := ((fun q => q+1, 2), "outside")
  for wire in [(false,0),(true,1)] do
    let (outcome, next) := Validation.traverseState guarded source [wire,(false,999)]
    unless outcome.toOption.isNone && next.1.1 2 == 3 && next.2 == "outside" do
      throw (IO.userError "refusal changed source or forced suffix")
  IO.println "FOCUSED-UNREACHABLE-SUFFIX-OK cases=2"

#print axioms Focus.compose
#print axioms Focus.modify_modify
#print axioms Focus.prototype_compose
#print axioms Focus.modify_commute
#print axioms Focus.checkedWith_frame
#print axioms Focus.checkedWith_installed
#print axioms Focus.checkedWith_outcome
#print axioms Factory.focus_get
#print axioms Factory.focus_identity
#print axioms Factory.focus_compose
end LeanPoo.Tests.FunctionalFocusedUpdate
