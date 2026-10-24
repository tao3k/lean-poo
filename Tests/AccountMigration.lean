import LeanPoo.Functional.AccountMigration

/-! Independent carrier-conversion, public-loss, graph-read coverage, complete
builder-refusal masks and approved warm-family controls. -/
namespace LeanPoo.Tests.AccountMigration
open Functional Functional.AccountMigration Functional.GeneralizedGraph

abbrev LegacyRaw := State String ConstructionWorkflow.Values

def legacy (amount : Int) (input : Option Int := some 9) : LegacyRaw := fun key =>
  if key == "total" then some (.ok amount) else if key == "input" then input.map Except.ok else none

def transferControls : Except String Unit := do
  match CarrierMigration.prepare (legacy 17 none) (graph 3 "private") (transfers 100) with
  | .error _ => throw "missing optional label"
  | .ok target =>
    unless (target.base .balance).bind Except.toOption == some 17 &&
        (target.base .label).bind Except.toOption == some "anonymous" &&
        (target.base .privateNote).bind Except.toOption == some "private" do throw "default/frame oracle"
  let missing : LegacyRaw := fun _ => none
  match CarrierMigration.prepare missing (graph 3 "private") (transfers 100) with
  | .error (.shape (.missingSource "total")) => pure ()
  | _ => throw "missing source"
  for amount in [-1,101] do
    match CarrierMigration.prepare (legacy amount) (graph 3 "private") (transfers 100) with
    | .error (.shape (.conversionFailed "total" .balance "balance-range")) => pure ()
    | _ => throw "range conversion"
  let failed : LegacyRaw := fun _ => some (.error (.source "source-failed"))
  let duplicate := [balanceTransfer 100,balanceTransfer 100]
  match CarrierMigration.prepare failed (graph 3 "private") duplicate with
  | .error (.shape (.duplicateTarget .balance)) => pure ()
  | _ => throw "whole shape must precede source failure"
  match CarrierMigration.prepare failed (graph 3 "private") (transfers 100) with
  | .error (.source "total" (.source "source-failed")) => pure ()
  | _ => throw "actual failed outcome"
  let failedLabel := fun key => if key == "input" then some (.error (.source "label-failed")) else legacy 17 (some 9) key
  match CarrierMigration.prepare failedLabel (graph 3 "private") (transfers 100) with
  | .error (.source "input" (.source "label-failed")) => pure ()
  | _ => throw "failed optional source cannot default"
  let computed : Transfer := {source := "total",target := .charge,convert := fun _ => .ok ⟨1⟩}
  match CarrierMigration.prepare failed (graph 3 "private") [computed] with
  | .error (.shape (.nonDataTarget .charge)) => pure ()
  | _ => throw "computed target overwrite"
  let unsupported := {graph 3 "private" with keys := [.rate,.charge,.label,.audit,.privateNote]}
  match CarrierMigration.prepare failed unsupported [balanceTransfer 100] with
  | .error (.shape (.unknownTarget .balance)) => pure ()
  | _ => throw "unknown target"
  -- Both successful data and exact source errors/absence cross representation.
  let wrap : (key : String) → Prototype.DictionaryBridge Int (Int × Unit) := fun _ =>
    ⟨fun value => (value,()),Prod.fst,fun _ => rfl,fun value => by cases value; rfl⟩
  let encoded := CarrierMigration.represent wrap failed
  match encoded "any" with
  | some (.error (.source "source-failed")) => pure ()
  | _ => throw "representation lost error"
  unless ((CarrierMigration.represent wrap (legacy 17)) "absent").isNone do throw "representation lost absence"

def projectionControls : Except String Unit := do
  let spec := graph 3 "private"
  unless (ProjectedSelf.check apiProjection spec).isOk do throw "valid projection"
  let hiddenValue := spec.define .audit (need .privateNote id)
  let hiddenPresence := spec.define .audit (.inspect .privateNote (fun _ present => .ok (toString present)))
  let hiddenNegative := spec.define .audit (.deny .privateNote (fun _ => .ok "absent"))
  let hiddenBranch := spec.define .audit (.choose (.pure (fun _ => true)) (fun _ value => value)
    (.pure (fun _ => .ok "selected")) (need .privateNote id))
  for candidate in [hiddenValue,hiddenPresence,hiddenNegative,hiddenBranch] do
    unless !(ProjectedSelf.check apiProjection candidate).isOk do throw "hidden dependency escaped"
  let raw := (graph 3 "first").base
  let changed := setSlot raw .privateNote (some (.ok "second"))
  unless (apiProjection.view (apiProjection.cook changed) .privateNote).isNone &&
      (changed .privateNote).bind Except.toOption == some "second" do throw "loss witness"
  unless (bridge.fromFields (apiProjection.cook changed)).balance.isNone do throw "representation cooking"

def capacity (input : Int) : Nat :=
  let freight := 2+input/5
  let cover := 3+input/7
  let reserve := 10*freight+cover
  (2+reserve/5+input/6+(1+input/4)).toNat

-- Stage invocation returns a new approved snapshot and preserves the other
-- generic's warmed definition/cache through existing family machinery.
def calls (account : Version) (balance rate fee : Nat) (label : String) : List Nat → Except String Nat
  | [] => .ok 0
  | units :: rest => match invoke account .spend units with
    | .error _ => .error "spend dispatch/admission"
    | .ok (result,warm) => do
      let expected := if units+fee ≤ balance then some (balance-(units+fee)) else none
      unless result.toOption == expected do throw "spend arithmetic"
      match invoke warm .receipt "customer" with
      | .error _ => throw "receipt dispatch/admission"
      | .ok (receipt,next) =>
        unless receipt.toOption == some ("customer/" ++ label ++ "/" ++ toString (balance*rate)) do throw "receipt arithmetic"
        return 2+(← calls next balance rate fee label rest)

def scenario (input : Int) (rate fee : Nat) : Except String Nat :=
  match ServiceMetadata.start {input} {} 10000 10000 with
  | .error _ => .error "legacy start"
  | .ok old => match ServiceMetadata.reserve old 2 with
    | .error _ => .error "legacy warm"
    | .ok warmed => match (migrate warmed.state rate {fee} 10000 (fun _ => true)).1 with
      | .error _ => .error "target start"
      | .ok account => do
        let balance := capacity input
        let label := "legacy-" ++ toString input
        unless account.approval.balance == balance && account.approval.rate == rate &&
            account.approval.label == label && account.candidate.cache.evaluated.length == 6 &&
            account.candidate.cache.reused.isEmpty &&
            (account.candidate.cache.closed.raw .audit).bind Except.toOption == some (label ++ ":" ++ toString (balance*rate)) do
          throw "target constructor oracle"
        let observations ← calls account balance rate fee label (List.range 41)
        let hidden := revise account [.setBase .privateNote (some (.ok "rotated"))] (· == .privateNote)
        match hidden.1 with
        | .error _ => throw "hidden edit"
        | .ok prepared =>
          unless prepared.candidate.cache.evaluated == [.privateNote] && prepared.candidate.cache.reused.length == 5 &&
              probes prepared.candidate == probes account.candidate do throw "hidden frame"
        for mask in List.range 64 do
          let migration := migrate warmed.state rate {fee} 10000 (fun key => mask.testBit (match key with
            | .balance => 0 | .rate => 1 | .charge => 2 | .label => 3 | .audit => 4 | .privateNote => 5))
          match migration.1,migration.2 with
          | .ok target,.inr retained =>
            unless mask == 63 && target.approval.balance == balance && retained.approval.balance == balance do
              throw "builder-mask accepted partial graph"
          | .error (.inr (.construction (.build _ _))),.inl retained =>
            unless mask != 63 &&
                ServiceBundle.reserveProbe retained.candidate == some ((balance : Int)-2,true) &&
                (retained.candidate.family.table.get? .reserve).map (fun generic => generic.cache.size) == some 1 do
              throw "builder-mask lost warm source"
          | _,_ => throw "builder-mask failure boundary"
        for policy in [{fee,broken := true},{fee,forbidden := true}] do
          let refused := migrate warmed.state rate policy 10000 (fun _ => true)
          match refused.1,refused.2 with
          | .error (.inr (.generic _)),.inl retained =>
            unless (retained.candidate.family.table.get? .reserve).map (fun generic => generic.cache.size) == some 1 do
              throw "generic refusal lost old cache"
          | _,_ => throw "target family refusal"
        match (migrate warmed.state 10001 {fee} 10000 (fun _ => true)).1 with
        | .error (.inr (.admission _ _ "charge-limit")) => pure ()
        | _ => throw "target admission refusal"
        let coverage := revise account [.define .audit (need .privateNote id)] (· == .audit)
        match coverage.1 with
        | .error (.admission _ _ "projection-coverage") =>
          unless probes coverage.2.candidate == probes account.candidate do throw "projection refusal changed account"
        | _ => throw "target cooked-self coverage"
        return observations

def check : Except String Nat := do
  transferControls
  projectionControls
  let mut count := 0
  for input in [0,1,7,15,30,50,80,120] do
    for rate in [1,3,9] do
      for fee in [0,1] do count := count+(← scenario input rate fee)
  return count

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"ACCOUNT-MIGRATION-CONTROLS-OK settings=48 calls={count} builder-masks=3072 accepted=48 refused=3024 hidden-rebuilt=1 retained=5"
end LeanPoo.Tests.AccountMigration
