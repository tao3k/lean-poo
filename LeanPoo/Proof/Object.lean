import LeanPoo.Proof.Invalidation
import LeanPoo.Proof.Batch
import LeanPoo.Object.Instance

namespace LeanPoo.Proof

/-- Reuse evaluated object slots outside a proved value-change footprint.
The patch frame and both instance equations establish the resolver equality
required by `Cache.rebase`; dependent computed slots must be included in
`patch.touched` whenever their resolved value changes. -/
def rebaseInstanceCache {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Object.Plan Key Value}
    (current : Object.Instance Key Value oldPlan)
    (next : Object.Instance Key Value newPlan)
    (patch : Patch Key (fun key => Option (Value key)))
    (aligned : next.state = patch.apply current.state)
    (keys : List Key)
    (cache : Object.Cache (current.prepare keys) current.state) :
    Object.Cache (next.prepare keys) next.state :=
  cache.rebase (next.prepare keys) next.state
    (fun key => key ∉ patch.touched) (by
      intro key untouched
      rw [(current.prepare keys).resolve_sound,
        (next.prepare keys).resolve_sound]
      change oldPlan.resolve key current.state =
        newPlan.resolve key next.state
      rw [current.agrees key, next.agrees key]
      exact ((congrFun aligned key).trans
        (patch.frame current.state key untouched)).symm)

/-- Reuse exactly the evaluated entries whose cached and new resolved values
compare equal. This checks computed dependents without a patch footprint and
does not recompute the old instance. -/
def rebaseInstanceCacheByValue {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Object.Plan Key Value}
    (current : Object.Instance Key Value oldPlan)
    (next : Object.Instance Key Value newPlan)
    (keys : List Key)
    (decideSame : (key : Key) → (value : Option (Value key)) →
      Decidable (value = (next.prepare keys).resolve key next.state))
    (cache : Object.Cache (current.prepare keys) current.state) :
    Object.Cache (next.prepare keys) next.state :=
  cache.rebaseByValue (next.prepare keys) next.state decideSame

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
