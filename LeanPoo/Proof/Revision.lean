import LeanPoo.Proof.Object
import LeanPoo.Object.Incremental

/-!
The object layer owns changed values and their finite dependency footprint.
This module projects that footprint into the existing proof-object patch and
certificate operations, without adding another slot evaluator.
-/

namespace LeanPoo.Proof

universe u v

/-- Treat a certified object revision as a patch that writes exactly the
finite value-change footprint. -/
def patchOfRevision {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    {spec : Object.Dependencies Key Value plan}
    {roots keys : List Key}
    (revision : Object.Revision spec roots keys)
    (obligations : List (Obligation Key (fun key => Option (Value key))) := []) :
    Patch Key (fun key => Option (Value key)) where
  apply := fun state key =>
    if key ∈ revision.touched then revision.instanceValue.state key
    else state key
  touched := revision.touched
  frame := by
    intro state key untouched
    simp [untouched]
  obligations := obligations

/-- The derived patch reproduces the revised fixed point, including keys
outside the finite declaration support. -/
theorem patchOfRevision_aligned {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Object.Plan Key Value}
    {spec : Object.Dependencies Key Value newPlan}
    {roots keys : List Key}
    (revision : Object.Revision spec roots keys)
    (current : Object.Instance Key Value oldPlan)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state)
    (obligations : List (Obligation Key (fun key => Option (Value key))) := []) :
    revision.instanceValue.state =
      (patchOfRevision revision obligations).apply current.state := by
  funext key
  by_cases touched : key ∈ revision.touched
  · simp [patchOfRevision, touched]
  · simp [patchOfRevision, touched]
    exact (revision.stableOutside current sameResolver key touched).symm

/-- Existing obligations that need repair, followed by obligations added by
this revision. -/
def pendingRevision {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Object.Plan Key Value}
    {spec : Object.Dependencies Key Value newPlan}
    {roots keys : List Key}
    (current : CertifiedObject Key Value oldPlan)
    (revision : Object.Revision spec roots keys)
    (obligations : List (Obligation Key (fun key => Option (Value key))) := []) :
    List (Obligation Key (fun key => Option (Value key))) :=
  pending (proofObjectOfInstance current.instanceValue current.obligations)
    (patchOfRevision revision obligations)

/-- Close a revised certified object using proofs only for the obligations
selected by the checked value-change footprint. -/
def CertifiedObject.applyRevision {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Object.Plan Key Value}
    {spec : Object.Dependencies Key Value newPlan}
    {roots keys : List Key}
    (current : CertifiedObject Key Value oldPlan)
    (revision : Object.Revision spec roots keys)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.instanceValue.state =
        newPlan.resolve key current.instanceValue.state)
    (obligations : List (Obligation Key (fun key => Option (Value key))) := [])
    (discharged : ∀ obligation,
      obligation ∈ pendingRevision current revision obligations →
      obligation.holds revision.instanceValue.state) :
    CertifiedObject Key Value newPlan :=
  current.applyPatch (patchOfRevision revision obligations)
    revision.instanceValue
    (patchOfRevision_aligned revision current.instanceValue sameResolver obligations)
    discharged

end LeanPoo.Proof
