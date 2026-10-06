import LeanPoo.Functional.ContractJoin

namespace LeanPoo.Tests.FunctionalContractJoin
open Functional Requirements
private def Value (_ : Nat) : Nat → Type
  | 2 => Bool
  | _ => Nat
private def keys : List Nat := [0,1,2]
private def Left (c : Nat) (data : Results Value c keys) := c ≤ data.1
private def Right (c : Nat) (data : Results Value c keys) := Nat.le data.1 data.2.1
private def Final (c : Nat) (data : Results Value c keys) := c ≤ data.2.1
private def fs (offset : Nat) : Factories Nat Value keys :=
  (fun c => c+offset, fun c => c+offset+2, fun _ => offset % 2 == 0, PUnit.unit)
private def left (offset : Nat) : Certified keys Left :=
  ⟨fs offset, fun c => by change c ≤ c+offset; omega⟩
private def right (offset : Nat) : Certified keys Right :=
  ⟨fs offset, fun c => by change c+offset ≤ c+offset+2; omega⟩
private theorem derive (c : Nat) (data : Results Value c keys)
    (proof : Left c data ∧ Right c data) : Final c data := Nat.le_trans proof.1 proof.2
private def construct (c : Nat) (data : Results Value c keys)
    (proof : Left c data ∧ Right c data) : {n : Nat // c ≤ n} :=
  ⟨data.2.1, derive c data proof⟩
private def run : IO Unit := do
  let mut reads := 0
  let mut hits := 0
  for offset in List.range 8 do
    let a := left offset
    let b := right offset
    let same : a.factories = b.factories := rfl
    for warm in [false,true] do
      for trace in [[0,0,1,0], [7,7,7], [23,24,23], [3,3,4,4]] do
        let mut original := ContextSlot.empty a
        let mut previous : Option Nat := none
        if warm then
          let c := trace.head!
          original := (original.read c).2.1
          previous := some c
        let mut slot := original.conjoin b same
        for c in trace do
          let actual := slot.consume construct c
          let baseline := (a.conjoin b same).consume construct c
          unless actual.1.val == c+offset+2 && actual.1.val == baseline.val &&
              actual.2.2 == (previous == some c) do
            throw (IO.userError "joined contract changed value or cache policy")
          let retained := actual.2.1.read c
          unless retained.2.2 &&
              (@BEq.beq Nat inferInstance retained.1.val.1 (c+offset)) &&
              (@BEq.beq Nat inferInstance retained.1.val.2.1 (c+offset+2)) &&
              (@BEq.beq Bool inferInstance retained.1.val.2.2.1 (offset % 2 == 0)) do
            throw (IO.userError "joined cache lost heterogeneous data")
          let final := (actual.2.1.entails Final derive).consume
            (fun _ data proof => (⟨data.2.1,proof⟩ : {n : Nat // _ ≤ n})) c
          unless final.2.2 && final.1.val == actual.1.val do
            throw (IO.userError "joined proofs cannot feed a derived consumer")
          slot := actual.2.1
          previous := some c
          reads := reads+1
          if actual.2.2 then hits := hits+1
  unless reads == 224 && hits == 112 do throw (IO.userError "joint corpus drift")
  IO.println s!"FUNCTIONAL-CONTRACT-JOIN-OK families=8 reads={reads} hits={hits} misses={reads-hits} traces=4 warmModes=2"
#eval run

-- A proof for another factory family cannot enter an existing cached snapshot.
example : True := by
  fail_if_success have bad := (left 0).conjoin (right 1) rfl
  fail_if_success have wrong : Snapshot (left 0) 9 := ((ContextSlot.empty (left 0)).read 0).1
  trivial
-- Left does not imply Right for arbitrary data; exact family admission is necessary.
example : ¬ (∀ data : Results Value 0 keys, Left 0 data → Right 0 data) := by
  intro assumed
  have conflict := assumed ((2 : Nat),(1 : Nat),true,PUnit.unit) (by change 0 ≤ 2; omega)
  change 2 ≤ 1 at conflict
  omega
#print axioms Certified.conjoin_factories
#print axioms Snapshot.conjoin_val
#print axioms ContextSlot.conjoin_empty
#print axioms ContextSlot.conjoin_retained
#print axioms ContextSlot.conjoin_hit
#print axioms ContextSlot.conjoin_consume
end LeanPoo.Tests.FunctionalContractJoin
