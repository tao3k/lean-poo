import LeanPoo.Functional.ServiceMetadata

/-! Quote ceilings and reservation conservation across selective graph edits
and policy-only releases. This advances generalized-MOP future work. -/
namespace LeanPoo.Examples.ServiceMetadata
open Functional Functional.ServiceBundle Functional.ServiceMetadata

-- Closing into a low-universe result keeps this executable despite the
-- dependent graph/cache receipts carried by published versions.
/-- Cache-sensitive admission inspects the exact successor. Probes in the
ordinary metadata approval do not themselves install their tentative caches. -/
def cacheCount {current : Request} (candidate : Candidate current) : Nat :=
  [Service.quote,.reserve,.cancel].foldl (fun count key =>
    count + ((candidate.family.table.get? key).map fun generic => generic.cache.size).getD 0) 0

def admitCached (maximum : Nat) (current : Request) (candidate : Candidate current) :
    Except String (Approval 100 current candidate) := do
  if maximum < cacheCount candidate then throw "cache-budget"
  admit 1000 100 current candidate

def checkCache : Except String Unit :=
  match ServiceMetadata.start {input := 30} {} 1000 100 with
  | .error error => .error (failureTag error)
  | .ok old => do
    match old.invoke model .quote ⟨"Delivery","US",1⟩ (admitCached 1) with
    | .error _ => throw "first admitted cache"
    | .ok (_,warm) =>
      unless cacheCount warm.candidate == 1 do throw "quote cache not installed"
      match warm.invoke model .reserve 2 (admitCached 1) with
      | .error (.inr "cache-budget") => pure ()
      | _ => throw "successful call bypassed joint admission"
      unless cacheCount warm.candidate == 1 do throw "refused cache escaped"
      match warm.invoke model .reserve 2 (admitCached 2) with
      | .error _ => throw "admitted second cache"
      | .ok (value,next) =>
        unless value.toOption == some (30,true) && cacheCount next.candidate == 2 do
          throw "second generic cache"
        unless ((next.candidate.family.table.get? .quote).map fun generic => generic.cache.recent) ==
            ((warm.candidate.family.table.get? .quote).map fun generic => generic.cache.recent) do
          throw "other generic changed"
    pure ()

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
    checkCache

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "SERVICE-METADATA-OK selective-revision, checked-reservation, quote-refusal, policy-reuse, exact-cache-admission"
#print axioms DeclarativeMetadata.Contract.invoke_accepts
#print axioms ServiceMetadata.reservation_conservation
#print axioms ServiceMetadata.reserve_construction
#print axioms ServiceMetadata.reserve_other
#print axioms ServiceMetadata.reserve_negative
#print axioms ServiceMetadata.declared_origin
#print axioms DeclarativeMetadata.Contract.invoke_logic
#print axioms ServiceMetadata.release_quote_bound
end LeanPoo.Examples.ServiceMetadata
