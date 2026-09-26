import LeanPoo.Proof.Invalidation
import LeanPoo.Proof.Batch
import LeanPoo.Object.Instance

namespace LeanPoo.Proof

/-- Proof obligations over the resolved object's values. -/
def proofObjectOfInstance {Key : Type} {Value : Key → Type}
    {plan : Object.Plan Key Value}
    (instanceValue : Object.Instance Key Value plan)
    (obligations : List (Obligation Key (fun key => Option (Value key)))) :
    ProofObject Key (fun key => Option (Value key)) :=
  ⟨instanceValue.state, obligations⟩

/-- Proofs bound to a C4-consistent typed object. -/
structure CertifiedObject (Key : Type) (Value : Key → Type)
    (plan : Object.Plan Key Value) where
  instanceValue : Object.Instance Key Value plan
  obligations : List (Obligation Key (fun key => Option (Value key)))
  certificate : Certificate (proofObjectOfInstance instanceValue obligations)

/-- Rebind an override to a new C4-valid object, supplying proofs only for
the obligations selected by the dependency filter. -/
def CertifiedObject.applyPatch {Key : Type} {Value : Key → Type}
    [DecidableEq Key] {plan nextPlan : Object.Plan Key Value}
    (current : CertifiedObject Key Value plan)
    (patch : Patch Key (fun key => Option (Value key)))
    (next : Object.Instance Key Value nextPlan)
    (aligned : next.state = patch.apply current.instanceValue.state)
    (discharged : ∀ obligation,
      obligation ∈ pending (proofObjectOfInstance current.instanceValue current.obligations) patch →
      obligation.holds next.state) :
    CertifiedObject Key Value nextPlan :=
  { instanceValue := next
    obligations := current.obligations ++ patch.obligations
    certificate := by
      have result := closePending
        (proofObjectOfInstance current.instanceValue current.obligations)
        patch current.certificate (by
          intro obligation membership
          simpa [append, proofObjectOfInstance, aligned] using
            discharged obligation membership)
      simpa [Certificate, proofObjectOfInstance, append, aligned] using result }

/-- Rebind an ordered batch of typed overrides to the next resolved object.
Repeated keys use the last supplied value; one dependency check covers the batch. -/
def CertifiedObject.applyValues {Key : Type} {Value : Key → Type}
    [DecidableEq Key] {plan nextPlan : Object.Plan Key Value}
    (current : CertifiedObject Key Value plan)
    (updates : List (Sigma (fun key => Option (Value key))))
    (obligations : List (Obligation Key (fun key => Option (Value key))))
    (next : Object.Instance Key Value nextPlan)
    (aligned : next.state =
      (Patch.setMany updates obligations).apply current.instanceValue.state)
    (discharged : ∀ obligation,
      obligation ∈ pending
        (proofObjectOfInstance current.instanceValue current.obligations)
        (Patch.setMany updates obligations) → obligation.holds next.state) :
    CertifiedObject Key Value nextPlan :=
  current.applyPatch (Patch.setMany updates obligations) next aligned discharged

end LeanPoo.Proof
