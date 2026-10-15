import LeanPoo.Functional.ServiceMetadata

/-! Quote ceilings and reservation conservation across selective graph edits
and policy-only releases. This advances generalized-MOP future work. -/
namespace LeanPoo.Examples.ServiceMetadata
open Functional Functional.ServiceBundle Functional.ServiceMetadata

-- Closing into a low-universe result keeps this executable despite the
-- dependent graph/cache receipts carried by published versions.
def check : Except String Unit :=
  match ServiceMetadata.start {input := 30} {} 1000 100 with
  | .error error => .error (failureTag error)
  | .ok initial => do
    match reserve initial 7 with
    | .error error => throw (reprStr error)
    | .ok receipt =>
      unless receipt.result.toOption == some (25,true) do throw "reservation conservation"
    let changed := ServiceMetadata.revise initial
      [.define "invoice" (ConstructionWorkflow.need "settlement" (· + 9))]
      (["invoice","release","total"].contains ·) 1000
    match changed.1 with
    | .error error => throw (failureTag error)
    | .ok prepared =>
      let version := prepared.snapshot model
      unless version.candidate.cache.evaluated.length == 3 && version.candidate.cache.reused.length == 12 do
        throw "selective graph construction"
      match reserve version 7 with
      | .error error => throw (reprStr error)
      | .ok receipt =>
        unless receipt.result.toOption == some (34,true) do throw "stale reservation metadata"
      -- Existing graph budget permits this invoice. The quote-level metadata
      -- rejects the whole family after construction, preserving the warm source.
      let refused := ServiceMetadata.revise version
        [.define "invoice" (ConstructionWorkflow.need "settlement" (· + 90))]
        (["invoice","release","total"].contains ·) 1000
      match refused.1 with
      | .ok _ => throw "quote ceiling escaped"
      | .error error =>
        unless failureTag error == "release-metadata" &&
            quoteProbe refused.2.candidate == some 78 do throw "partial publication"
      let peak := ServiceMetadata.revise version [.policy {pricing := .peak}] (fun _ => false) 1000
      match peak.1 with
      | .error error => throw (failureTag error)
      | .ok prepared =>
        unless prepared.candidate.cache.evaluated.isEmpty &&
            prepared.candidate.cache.reused.length == 15 && quoteProbe prepared.candidate == some 52 do
          throw "policy-only declaration refresh"
    pure ()

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "SERVICE-METADATA-OK selective-revision, checked-reservation, quote-refusal, policy-reuse"
#print axioms DeclarativeMetadata.Contract.invoke_accepts
#print axioms ServiceMetadata.reservation_conservation
#print axioms ServiceMetadata.reserve_construction
#print axioms ServiceMetadata.declared_origin
#print axioms DeclarativeMetadata.Contract.invoke_logic
#print axioms ServiceMetadata.release_quote_bound
end LeanPoo.Examples.ServiceMetadata
