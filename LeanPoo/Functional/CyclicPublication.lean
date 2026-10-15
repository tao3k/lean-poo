import LeanPoo.Functional.PositiveEquations
import LeanPoo.Functional.CarrierMigration

/-! Least positive cyclic closure followed by existing heterogeneous family
construction and exact-candidate admission. Pure finite future-work extension. -/
namespace LeanPoo.Functional.CyclicPublication
open PositiveEquations
variable {n : Nat} {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : StagedPublication.Model (Fin n) (fun _ => Bool) G Policy Cooked Args Method Result)
variable {Approved : (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) →
  StagedPublication.Candidate model current → Type} {AdmissionIssue : Type}

structure Version where
  equations : Equations n
  snapshot : StagedPublication.Snapshot model Approved
  origin : snapshot.request.graph = declaration equations
  canonical : snapshot.candidate.cache.closed.raw = raw (close equations).value

def prepare (equations : Equations n) (policy : Policy)
    (admit : (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) →
      (candidate : StagedPublication.Candidate model current) → Except AdmissionIssue (Approved current candidate)) :
    Except (StagedPublication.Failure (BuildError := Unit) (AdmissionError := AdmissionIssue) model)
      (Version (Approved := Approved) model) :=
  match built : StagedPublication.finish model ⟨declaration equations,policy⟩ (materialize equations) admit with
  | .error error => .error error
  | .ok prepared => .ok ⟨equations,prepared.snapshot model,rfl,by
      change prepared.candidate.cache.closed.raw = _
      rw [StagedPublication.finish_cache model _ _ admit prepared built]
      rfl⟩

theorem prepare_equations (equations : Equations n) (policy : Policy)
    (admit : (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) →
      (candidate : StagedPublication.Candidate model current) → Except AdmissionIssue (Approved current candidate))
    (version : Version (Approved := Approved) model)
    (prepared : prepare model equations policy admit = .ok version) : version.equations = equations := by
  unfold prepare at prepared
  split at prepared
  · contradiction
  · cases prepared; rfl

/-- Every revision recomputes least closure from bottom. Old true facts or an
arbitrary warm fixed point cannot bootstrap an unsupported new cyclic fact. -/
def publish (old : Version (Approved := Approved) model) (equations : Equations n) (policy : Policy) (admit :
    (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) → (candidate : StagedPublication.Candidate model current) →
      Except AdmissionIssue (Approved current candidate)) :=
  CarrierMigration.publish old (fun _ => prepare model equations policy admit)

/-- Calls refresh existing candidate-bound approvals and retain the exact least
cyclic solution and source equation declarations through cache warming. -/
def Version.invoke (old : Version (Approved := Approved) model) (key : G) (args : Args key)
    (admit : (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) →
      (candidate : StagedPublication.Candidate model current) → Except AdmissionIssue (Approved current candidate)) :
    Except (Sum (Object.DispatchTableError G) AdmissionIssue) (Result key × Version (Approved := Approved) model) :=
  match called : old.snapshot.invoke model key args admit with
  | .error error => .error error
  | .ok (result,next) =>
    let unchanged := StagedPublication.Snapshot.invoke_construction model old.snapshot key args admit result next called
    .ok (result,⟨old.equations,next,by rw [unchanged.1]; exact old.origin,
      unchanged.2.1.trans old.canonical⟩)

theorem Version.invoke_equations (old : Version (Approved := Approved) model) (key : G) (args : Args key)
    (admit : (current : GeneralizedMOP.Request (Fin n) (fun _ => Bool) Policy) →
      (candidate : StagedPublication.Candidate model current) → Except AdmissionIssue (Approved current candidate))
    (result : Result key) (next : Version (Approved := Approved) model)
    (called : old.invoke model key args admit = .ok (result,next)) : next.equations = old.equations := by
  unfold Version.invoke at called
  split at called
  · contradiction
  · cases called; rfl

omit [DecidableEq G] in
/-- Canonicality is stronger than satisfying the equations: every Boolean fixed
point of the same source contains all published facts. -/
theorem Version.least (version : Version (Approved := Approved) model) (other : Bits n)
    (fixed : step version.equations other = other) (index : Fin n)
    (present : version.snapshot.candidate.cache.closed.raw index = some (.ok true)) : other index = true := by
  rw [version.canonical] at present
  have fact : (close version.equations).value index = true := by simpa [raw] using present
  exact PositiveEquations.least _ other fixed index fact

end LeanPoo.Functional.CyclicPublication
