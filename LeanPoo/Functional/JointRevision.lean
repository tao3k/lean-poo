import LeanPoo.Functional.JointPublication
import LeanPoo.Functional.GraphRevision

/-! Dependent endpoint and approval replacements prepare one immutable candidate.
Component support belongs to each head; no partial projection is published. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Endpoint] [DecidableEq Policy]
/-- Unique typed replacement lists stage heterogeneous heads and approvals together. -/
structure Revision (current : Bundle Id Endpoint Policy Head Metadata) where
  id : Id
  heads : List ((key : Endpoint) × Head key)
  approvals : List ((key : Policy) × Metadata key)
  uniqueHeads : (heads.map Sigma.fst).Nodup
  uniqueApprovals : (approvals.map Sigma.fst).Nodup
/-- Prepare a candidate without modifying any current endpoint or policy value. -/
def Revision.apply {current : Bundle Id Endpoint Policy Head Metadata} (revision : Revision current) :=
  Bundle.mk revision.id
    (fun key => (GeneralizedGraph.selectEdit revision.heads key).getD (current.heads key))
    (fun key => (GeneralizedGraph.selectEdit revision.approvals key).getD (current.approvals key))
/-- Submitted head replacement carries its actual dependent component carrier. -/
theorem Revision.head_at {current : Bundle Id Endpoint Policy Head Metadata} (revision : Revision current)
    (key : Endpoint) (value : Head key) (member : ⟨key,value⟩ ∈ revision.heads) :
    revision.apply.heads key = value := by
  simp [apply,GeneralizedGraph.selectEdit_at revision.heads key value revision.uniqueHeads member]
/-- Shared or local metadata replacement is the actual submitted dependent value. -/
theorem Revision.approval_at {current : Bundle Id Endpoint Policy Head Metadata} (revision : Revision current)
    (key : Policy) (value : Metadata key) (member : ⟨key,value⟩ ∈ revision.approvals) :
    revision.apply.approvals key = value := by
  simp [apply,GeneralizedGraph.selectEdit_at revision.approvals key value revision.uniqueApprovals member]
/-- Omitted endpoint replacements retain the complete current head, including support. -/
theorem Revision.head_frame {current : Bundle Id Endpoint Policy Head Metadata} (revision : Revision current)
    (key : Endpoint) (missing : key ∉ revision.heads.map Sigma.fst) : revision.apply.heads key = current.heads key := by
  simp [apply,GeneralizedGraph.selectEdit_none revision.heads key missing]
/-- Omitted approval values retain identity independently of other shared changes. -/
theorem Revision.approval_frame {current : Bundle Id Endpoint Policy Head Metadata} (revision : Revision current)
    (key : Policy) (missing : key ∉ revision.approvals.map Sigma.fst) :
    revision.apply.approvals key = current.approvals key := by
  simp [apply,GeneralizedGraph.selectEdit_none revision.approvals key missing]
end LeanPoo.Functional.JointPublication
