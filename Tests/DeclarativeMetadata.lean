import LeanPoo.Functional.ServiceMetadata

/-! Independent Boolean, arithmetic and rejection controls for declarative
metadata and real graph/family publication. No native admission. -/
namespace LeanPoo.Tests.DeclarativeMetadata
open Functional Functional.DeclarativeMetadata Functional.ServiceBundle Functional.ServiceMetadata

abbrev Action := ConstructionWorkflow.Action (Int × Bool)

def checkLogic : Except String Nat := do
  let mut count := 0
  for mask in List.range 8 do
    let meaning : Fin 3 → Prop := fun key => mask.testBit key.val = true
    let formulas : List (Formula (Fin 3) × Bool) := [
      (.truth,true), (.atom 0,mask.testBit 0),
      (.both (.atom 0) (.atom 1),mask.testBit 0 && mask.testBit 1),
      (.either (.atom 0) (.atom 1),mask.testBit 0 || mask.testBit 1),
      (.implies (.atom 0) (.atom 1),!(mask.testBit 0) || mask.testBit 1),
      (.deny (.atom 0),!(mask.testBit 0)),
      (.both (.implies (.atom 0) (.atom 1)) (.either (.deny (.atom 1)) (.atom 2)),
        (!(mask.testBit 0) || mask.testBit 1) && (!(mask.testBit 1) || mask.testBit 2))]
    for (formula,expected) in formulas do
      unless (formula.check meaning).isOk == expected do throw "formula truth table"
      count := count+1
  return count

def contractControls : Except String Unit := do
  let contract := reservation 10
  -- Domain failure wins even if the underlying execution would fail.
  match contract.invoke (fun _ => (Except.error "dispatch" : Except String (Action × Nat))) 0 with
  | .error (.input "positive-units") => pure ()
  | _ => throw "input precedence"
  match contract.invoke (fun _ => (Except.error "dispatch" : Except String (Action × Nat))) 1 with
  | .error (.source "dispatch") => pure ()
  | _ => throw "source identity"
  -- An inner source error remains a value of the actual result carrier and is
  -- rejected by the output refinement, rather than relabelled dispatch error.
  match contract.invoke (fun _ => (.ok (.error "business",7) : Except String (Action × Nat))) 1 with
  | .error (.output "successful-reservation") => pure ()
  | _ => throw "nested source boundary"
  match contract.invoke (fun _ => (.ok (.ok (-1,true),7) : Except String (Action × Nat))) 1 with
  | .error (.output "successful-reservation") => pure ()
  | _ => throw "output precedence"
  match contract.invoke (fun _ => (.ok (.ok (8,true),7) : Except String (Action × Nat))) 1 with
  | .error .logic => pure ()
  | _ => throw "conservation admission"
  match contract.invoke (fun _ => (.ok (.ok (9,true),7) : Except String (Action × Nat))) 1 with
  | .ok receipt => unless receipt.state == 7 && receipt.result.toOption == some (9,true) do throw "state identity"
  | _ => throw "valid contract"

/-- Mixed declaration order, guard selection and erasure use the actual existing
multimethod, rather than comparing two copies of the metadata interpreter. -/
def methodControls : Except String Unit := do
  let seed : Object.Multimethod Nat (Nat → Int) Int := {
    arity := 1
    precedence := fun _ => [["Derived","Base"]]
    combine := fun methods args => methods.foldl (fun sum method => sum+method args) 0 }
  let declarations : List (Declaration Nat (Nat → Int)) := [
    .replace "base" [.prototype "Base"] (fun _ => 3),
    .contribute "base.extra" [.prototype "Base"] (fun _ => 5),
    .guarded "derived" [.prototype "Derived"] (fun units => units > 2) (fun _ => 11)]
  match install seed declarations with
  | .error _ => throw "declaration installation"
  | .ok generic =>
    unless (generic.call 1).toOption.map Prod.fst == some 8 &&
        (generic.call 4).toOption.map Prod.fst == some 19 do throw "guard/combination"
    match install generic [.remove "remove-base" [.prototype "Base"]] with
    | .error _ => throw "declaration erase"
    | .ok erased =>
      unless (erased.call 1).toOption.map Prod.fst == some 0 do throw "erase selection"
  match install seed [.replace "invalid" [] (fun _ => 1)] with
  | .error (.arity 1 0) => pure ()
  | _ => throw "arity refusal"

-- Numerical oracle deliberately does not call ConstructionWorkflow's resolver.
def capacity (input : Int) : Int :=
  let freight := 2+input/5
  let cover := 3+input/7
  let reserve := 10*freight+cover
  let tax := 2+reserve/5
  let risk := input/6
  tax+risk+(1+input/4)

def scenario (input : Int) (peak : Bool) : Except String Nat :=
  match ServiceMetadata.start {input} {pricing := if peak then .peak else .aggregate} 1000 1000 with
  | .error error => .error (failureTag error)
  | .ok version => do
    let total := capacity input
    unless version.approval.business.total == total do throw "capacity oracle"
    let mut count := 0
    for units in List.range 81 do
      match reserve version units with
      | .error error =>
        let expected := if units == 0 then "input" else "output"
        let actual := match error with
          | .input _ => "input" | .output _ => "output" | _ => "other"
        unless (units == 0 || (units : Int) > total) && actual == expected do throw "reservation refusal"
      | .ok receipt =>
        unless units > 0 && (units : Int) ≤ total &&
            receipt.result.toOption == some (total-(units : Int),true) do throw "reservation oracle"
        -- A second call runs on the actual warmed family returned by the receipt.
        match reserve receipt.state units with
        | .error _ => throw "warm contract"
        | .ok next =>
          unless next.result.toOption == receipt.result.toOption do throw "warm parity"
          if units == 2 then
            let refused := ServiceMetadata.revise next.state [.policy {forbiddenCancel := true}] (fun _ => false) 1000
            match refused.1 with
            | .error (.generic (.negative .cancel _ _)) =>
              let before := next.state.candidate.family.table.get? .reserve
              let after := refused.2.candidate.family.table.get? .reserve
              unless before.map (fun generic => generic.cache.size) == some 1 &&
                  after.map (fun generic => generic.cache.size) == some 1 do throw "warm old cache lost"
            | _ => throw "warm atomic refusal"
      count := count+1
    -- A candidate can pass existing graph/business approval but exceed the
    -- separate quote ceiling. Both start and revision use actual joint checks.
    match ServiceMetadata.start {input} {pricing := if peak then .peak else .aggregate} 1000 0 with
    | .error (.admission _ _ "release-metadata") => pure ()
    | _ => throw "release ceiling refusal"
    let revised := ServiceMetadata.revise version [.policy {pricing := if peak then .aggregate else .peak}]
      (fun _ => false) 1000
    match revised.1 with
    | .error error => throw (failureTag error)
    | .ok prepared =>
      unless prepared.candidate.cache.evaluated.isEmpty && prepared.candidate.cache.reused.length == 15 do
        throw "policy-only reuse"
    let refused := ServiceMetadata.revise version [.policy {forbiddenCancel := true}] (fun _ => false) 1000
    match refused.1 with
    | .error (.generic (.negative .cancel _ _)) =>
      unless quoteProbe refused.2.candidate == quoteProbe version.candidate &&
          cancelProbe refused.2.candidate == cancelProbe version.candidate do throw "atomic refusal"
    | _ => throw "negative-watch precedence"
    return count

def check : Except String Nat := do
  let truth ← checkLogic
  contractControls
  methodControls
  let mut calls := 0
  for input in [0,1,7,15,30,50,80,120] do
    for peak in [false,true] do calls := calls + (← scenario input peak)
  return truth+calls

def run : IO Unit := match check with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"DECLARATIVE-METADATA-OK {count} observations; typed calls, truth tables, method edits and atomic refusals"
#eval run
end LeanPoo.Tests.DeclarativeMetadata
