import LeanPoo.Functional.AccountMigration

/-! Warm settlement -> typed account -> hidden-data revision, with lossy cooked
self closure and atomic refusal at conversion, coverage and generic admission. -/
namespace LeanPoo.Examples.AccountMigration
open Functional Functional.AccountMigration

def check : Except String Unit :=
  match ServiceMetadata.start {input := 30} {} 1000 1000 with
  | .error _ => .error "legacy start"
  | .ok initial => match ServiceMetadata.reserve initial 2 with
    | .error _ => .error "legacy warm"
    | .ok warm => match (migrate warm.state 3 {fee := 1} 1000 (fun _ => true)).1 with
      | .error _ => .error "carrier migration"
      | .ok account => do
        unless account.approval.balance == 32 && account.approval.rate == 3 &&
            account.candidate.cache.evaluated.length == 6 && account.candidate.cache.reused.isEmpty &&
            probes account.candidate == (some 29,some "customer/legacy-30/96") do throw "target oracle"
        unless (apiProjection.view account.candidate.interface .privateNote).isNone &&
            (account.candidate.cache.closed.raw .privateNote).isSome do throw "public projection retained private note"
        match invoke account .spend 5 with
        | .error _ => throw "account warm"
        | .ok (result,hot) =>
          unless result.toOption == some 26 do throw "spend oracle"
          let edited := revise hot [.setBase .privateNote (some (.ok "rotated-private"))] (· == .privateNote)
          match edited.1 with
          | .error _ => throw "hidden revision"
          | .ok prepared =>
            let next := prepared.snapshot model
            unless next.candidate.cache.evaluated == [.privateNote] && next.candidate.cache.reused.length == 5 &&
                probes next.candidate == probes hot.candidate do throw "hidden frame/reuse"
            let refused := revise next [.define .audit (need .privateNote id)] (· == .audit)
            match refused.1 with
            | .error (.admission _ _ "projection-coverage") =>
              unless probes refused.2.candidate == probes next.candidate do throw "partial lossy publication"
            | _ => throw "unobservable final-self read admitted"
        -- A rejected target conversion keeps the complete old warm family.
        let refused := migrate warm.state 3 {} 0 (fun _ => true)
        match refused.1,refused.2 with
        | .error (.inl (.shape (.conversionFailed "total" .balance "balance-range"))),.inl retained =>
          unless ServiceBundle.quoteProbe retained.candidate == ServiceBundle.quoteProbe warm.state.candidate do
            throw "source changed on migration refusal"
        | _,_ => throw "conversion refusal"
        pure ()

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "ACCOUNT-MIGRATION-OK cross-carrier=Int/Nat/Money public-loss=true hidden-rebuilt=1 retained=5"
#print axioms ProjectedSelf.step
#print axioms CarrierMigration.rebuild_origin
#print axioms CarrierMigration.apply_head
#print axioms CarrierMigration.publish_refused
#print axioms AccountMigration.lossy
#print axioms AccountMigration.migrated_balance
end LeanPoo.Examples.AccountMigration
