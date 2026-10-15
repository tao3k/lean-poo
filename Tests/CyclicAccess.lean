import LeanPoo.Functional.CyclicAccess

/-! Independent quorum arithmetic, full source/configuration matrix, actual
warm caches and atomic first-refusal controls for cyclic service publication. -/
namespace LeanPoo.Tests.CyclicAccess
open Functional Functional.CyclicAccess

def expected (config : Config) (enabled : Bool) : List Bool :=
  let member := enabled && config.trust
  let quorum := (if config.training then 1 else 0)+(if config.team then 1 else 0)+(if config.compliance then 1 else 0)
  let approved := member && decide (2 ≤ quorum)
  let team := approved && config.team
  let compliance := member && config.compliance
  let release := team && compliance
  [enabled,enabled,member,config.training,approved,approved,team,release,compliance,approved]

def active (config : Config) (enabled : Bool) : List Nat :=
  ((expected config enabled).zipIdx.filter (fun pair => pair.1)).map Prod.snd

def memoState (version : Version attestation) := (version.memo.entries.map (·.input),version.memo.statistics)
def familyState (version : Version attestation) :=
  ((version.closure.snapshot.candidate.family.table.get? .grant).map (fun generic => generic.cache.size),
   (version.closure.snapshot.candidate.family.table.get? .explain).map (fun generic => generic.cache.size))

def checkVersion (version : Version attestation) (config : Config) (enabled : Bool) : Except String Unit := do
  let actual := List.ofFn fun index : Fin 10 => bit version.closure.snapshot.candidate.cache.closed.raw index
  unless actual == expected config enabled && version.closure.snapshot.candidate.interface.active == active config enabled &&
      version.enabled == enabled && version.closure.snapshot.candidate.cache.reused.isEmpty &&
      version.closure.snapshot.candidate.cache.evaluated.isEmpty do throw "cyclic arithmetic/least/builder boundary"

def scenario (config : Config) (enabled : Bool) (depth : Nat) : Except String Nat :=
  let role := if enabled then "active" else "revoked"
  match start attestation (depth,role) 200 config {} with
  | .error _ => .error "initial source/closure"
  | .ok initial => do
    checkVersion initial config enabled
    unless initial.memo.statistics.misses == depth+1 && initial.memo.statistics.hits == depth do
      throw "shared recursive source oracle"
    match invoke attestation initial .grant ("customer",true) with
    | .error _ => throw "grant outer failure"
    | .ok (result,grantWarm) =>
      let release := (expected config enabled)[7]!
      match result with
      | .ok value => unless release && value == "release:customer" do throw "grant oracle"
      | .error reason => unless !release && reason == "not-authorized" do throw "denial oracle"
      match invoke attestation grantWarm .explain () with
      | .error _ => throw "explain outer failure"
      | .ok (keys,warm) =>
        unless keys == active config enabled && familyState warm == (some 1,some 1) do throw "warm family"
        checkVersion warm config enabled
        match invoke attestation warm .grant ("customer",false) with
        | .ok (.error "consent",_) => pure ()
        | _ => throw "call-level source error"
        let nextConfig : Config := {config with trust := !config.trust}
        let changed := revise attestation warm (depth,role) 1 nextConfig {}
        match changed.1,changed.2 with
        | .ok next,.inr published =>
          checkVersion next nextConfig enabled
          unless memoState next == memoState published && next.memo.statistics.misses == warm.memo.statistics.misses &&
              next.memo.statistics.hits == warm.memo.statistics.hits+1 && familyState next == (some 0,some 0) do
            throw "safe source reuse versus fresh cyclic family"
        | _,_ => throw "hot source policy change"
        -- Switch attestation, keep all other configuration and source program.
        let nextRole := if enabled then "revoked" else "active"
        match (revise attestation warm (depth,nextRole) 200 config {}).1 with
        | .error _ => throw "source change"
        | .ok next => checkVersion next config (!enabled)
        let variants := [
          revise attestation warm (depth+20,"active") 0 config {},
          revise attestation warm (0,"cycle") 50 config {},
          revise attestation warm (0,"failed") 20 config {},
          revise attestation warm (depth,role) 1 config {broken := true},
          revise attestation warm (depth,role) 1 config {forbidden := true},
          revise attestation warm (depth,role) 1 config {corrupt := true}]
        for (attempt,index) in variants.zipIdx do
          match attempt.1,attempt.2 with
          | .error error,.inl old =>
            let tag := match error with
              | .recursive _ .budgetExhausted => 0
              | .recursive _ (.cycle _ _) => 1
              | .source "attestation-source" => 2
              | .publication (.generic (.registration _ _)) => 3
              | .publication (.generic (.negative _ _ _)) => 4
              | .publication (.admission _ _ "coherence") => 5
              | _ => 99
            unless tag == index && memoState old == memoState warm && familyState old == familyState warm &&
                probes old.closure.snapshot.candidate == probes warm.closure.snapshot.candidate do
              throw "failure kind/order/whole warm snapshot"
          | _,_ => throw "invalid publication accepted"
        -- A false source answer is a valid solution. A separate release policy
        -- can reject it, while preserving the old complete warm snapshot.
        let refused := revise attestation warm (depth,"revoked") 200 config {requireRelease := true}
        match refused.1,refused.2 with
        | .error (.publication (.admission _ _ "release-required")),.inl old =>
          unless memoState old == memoState warm && familyState old == familyState warm do throw "required release frame"
        | _,_ => throw "required release admitted false attestation"
        return 3

def check : Except String Nat := do
  let mut count := 0
  for mask in List.range 16 do
    let config : Config := ⟨mask.testBit 0,mask.testBit 1,mask.testBit 2,mask.testBit 3⟩
    for enabled in [false,true] do
      for depth in [0,3] do count := count+(← scenario config enabled depth)
  return count

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"CYCLIC-ACCESS-CONTROLS-OK settings=64 calls={count} accepted-revisions=128 refused-revisions=448 exact-warm-source=true"
end LeanPoo.Tests.CyclicAccess
