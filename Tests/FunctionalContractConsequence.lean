import LeanPoo.Functional.ContractConsequence

namespace LeanPoo.Tests.FunctionalContractConsequence
open Functional Requirements
private def Value (c : Nat) : Nat → Type
  | 0 => {n : Nat // c ≤ n}
  | _ => Nat
private def keys : List Nat := [0,1]
private def Claim (c : Nat) (data : Results Value c keys) := data.1.val+1 ≤ data.2.1
private def Next (c : Nat) (data : Results Value c keys) := data.1.val ≤ data.2.1
private def Final (c : Nat) (data : Results Value c keys) := c ≤ data.2.1
private theorem derive (c : Nat) (data : Results Value c keys) (proof : Claim c data) : Next c data := by
  unfold Claim Next at *; omega
private theorem finish (c : Nat) (data : Results Value c keys) (proof : Next c data) : Final c data :=
  Nat.le_trans data.1.property proof
private def ready (offset : Nat) : Certified keys Claim :=
  ⟨(fun c => ⟨c+offset, by omega⟩, fun c => c+offset+2, PUnit.unit), fun c => by
    change c+offset+1 ≤ c+offset+2; omega⟩
private def construct (c : Nat) (data : Results Value c keys) (proof : Next c data) : {n : Nat // c ≤ n} :=
  ⟨data.2.1, finish c data proof⟩
private def run : IO Unit := do
  let mut reads := 0
  let mut hits := 0
  for offset in List.range 8 do
    let original := ready offset
    for warm in [false,true] do
      for trace in [[0,0,1,1,0,0], [7,7,7], [23,24,25]] do
        let mut broad := ContextSlot.empty original
        let mut previous : Option Nat := none
        if warm then
          let c := trace.head!
          broad := (broad.read c).2.1
          previous := some c
        let mut slot := broad.entails Next derive
        for c in trace do
          let actual := slot.consume construct c
          let expected := original.consume (fun c data proof => construct c data (derive c data proof)) c
          unless actual.1.val == c+offset+2 && actual.1.val == expected.val &&
              actual.2.2 == (previous == some c) do
            throw (IO.userError "contract consequence changed value or cache policy")
          let data := (actual.2.1.read c).1
          unless (@BEq.beq Nat inferInstance data.val.1.val (c+offset)) &&
              (@BEq.beq Nat inferInstance data.val.2.1 (c+offset+2)) do
            throw (IO.userError "consequence changed retained dependent values")
          let chained := actual.2.1.entails Final finish
          let result := chained.consume (fun _ data proof => (⟨data.2.1,proof⟩ : {n : Nat // _ ≤ n})) c
          unless result.2.2 && result.1.val == c+offset+2 do
            throw (IO.userError "chained consequence lost retained hit or joint proof")
          slot := actual.2.1
          previous := some c
          reads := reads+1
          if actual.2.2 then hits := hits+1
  unless reads == 192 && hits == 104 do throw (IO.userError "contract corpus drift")
  IO.println s!"FUNCTIONAL-CONTRACT-CONSEQUENCE-OK families=8 reads={reads} hits={hits} misses={reads-hits} traces=3 warmModes=2"
#eval run

example (offset : Nat) :
    ((ready offset).entails Next derive).entails Final finish =
      (ready offset).entails Final (fun c data proof => finish c data (derive c data proof)) :=
  Certified.entails_trans _ _ _ _ _
-- A logical consequence cannot replace the original dependent data or invent a proof.
example : True := by
  fail_if_success have bad := (ready 0).entails (fun _ _ => False) (fun _ _ proof => proof)
  fail_if_success have wrong : Snapshot (ready 0) 9 := ((ContextSlot.empty (ready 0)).read 0).1
  trivial
#print axioms Certified.entails_factories
#print axioms Certified.entails_trans
#print axioms Snapshot.entails_val
#print axioms ContextSlot.entails_empty
#print axioms ContextSlot.entails_retained
#print axioms ContextSlot.entails_hit
#print axioms ContextSlot.entails_consume
end LeanPoo.Tests.FunctionalContractConsequence
