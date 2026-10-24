import LeanPoo.Functional.CyclicAccess

/-! Shared safe recursion, quorum/group cycles and atomic warm-family revision.
Completed false attestation is a valid least solution; divergence is a separate
recursive input refusal. This advances generalized-MOP future work. -/
namespace LeanPoo.Examples.CyclicAccess
open Functional Functional.CyclicAccess

def check : Except String Unit :=
  match start attestation (4,"active") 200 {} {requireRelease := true} with
  | .error _ => .error "attested cyclic start"
  | .ok initial => match invoke attestation initial .grant ("customer",true) with
    | .error _ => .error "grant warm"
    | .ok (result,warm) => do
      unless result.toOption == some "release:customer" && warm.memo.statistics.misses == 5 &&
          warm.memo.statistics.hits ≥ 4 do throw "shared recursion or grant"
      -- Same program/request uses its safe memo; changed trust is re-solved
      -- from bottom rather than reusing an old, larger cyclic fixed point.
      let changed := revise attestation warm (4,"active") 1 {trust := false} {}
      match changed.1,changed.2 with
      | .ok next,.inr published =>
        unless !next.closure.snapshot.candidate.interface.release &&
            published.memo.statistics.misses == warm.memo.statistics.misses &&
            published.memo.statistics.hits == warm.memo.statistics.hits+1 do throw "hot source or least revision"
      | _,_ => throw "supported policy revision"
      let revoked := revise attestation warm (4,"revoked") 200 {} {}
      match revoked.1 with
      | .error _ => throw "completed false attestation refused"
      | .ok next =>
        unless !next.closure.snapshot.candidate.interface.release &&
            next.closure.snapshot.candidate.interface.active == [3] do throw "cycle manufactured authority"
      let refused := revise attestation warm (4,"revoked") 200 {} {requireRelease := true}
      match refused.1,refused.2 with
      | .error (.publication (.admission _ _ "release-required")),.inl old =>
        unless old.memo.statistics == warm.memo.statistics &&
            probes old.closure.snapshot.candidate == probes warm.closure.snapshot.candidate do throw "partial rejected revision"
      | _,_ => throw "required-release refusal"
      match (revise attestation warm (0,"cycle") 50 {} {}).1 with
      | .error (.recursive _ (.cycle _ _)) => pure ()
      | _ => throw "recursive divergence confused with equation closure"
      pure ()

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "CYCLIC-ACCESS-OK safe-shared-attestation quorum least-cycles revision revocation atomic-refusal"
#print axioms Prototype.FiniteClosure.close
#print axioms Prototype.FiniteClosure.stable
#print axioms PositiveEquations.closed
#print axioms PositiveEquations.least_unique
#print axioms CyclicPublication.Version.least
#print axioms CyclicAccess.attestation_active
#print axioms CyclicAccess.observed_source
#print axioms CyclicAccess.revoked
end LeanPoo.Examples.CyclicAccess
