import LeanPoo.C4.VerifiedOrder
import LeanPoo.C4.OrderRelation
import LeanPoo.C4.Renaming
import LeanPoo.C4.OrdinaryNode
import LeanPoo.C4.AuditedResolver
import LeanPoo.C4.Diagnostics
import LeanPoo.Proof.Reuse
import LeanPoo.Proof.Batch

/-! Generic client contracts mirrored in docs/reusable-contracts.org. These
check how consumers combine the public API, independently of a demo domain. -/
namespace LeanPoo.Tests.ReusableContracts
open C4 Proof

example (success : linearizeAudited graph root = .ok output) :
    ∃ tail, GraphTrace graph root output tail := linearizeAudited_graph_sound success


/- A client may choose ordinary computation plus audits without losing any
checked successful output. Exact failure diagnostics are kept separately. -/
example (checked : linearizeChecked graph root = .ok output) :
    linearizeAudited graph root = .ok output := linearizeAudited_checked_complete checked

example : ((linearizeAuditedVerified graph root).map (·.output)).toOption =
    (linearizeChecked graph root).toOption := linearizeAuditedVerified_toOption

example (receipt : RejectedOrder graph root) : ¬ Nonempty (VerifiedOrder graph root) :=
  receipt.noVerified

example (receipt : RejectedOrder graph root) (unique : (graph.nodes.map Node.name).Nodup) :
    ¬ ∃ output tail, GraphTrace graph root output tail :=
  receipt.noGraphTrace (LinearizeState.reachableUnique_of_global unique)

example : ((diagnoseAudited graph root).mapError (·.error)).map (·.output) =
    linearizeAudited graph root := diagnoseAudited_projection

example (order : VerifiedOrder graph root) (query : String)
    (present : order.indexAncestors.isAncestor query = true) : Ancestor graph query root :=
  order.indexAncestors.isAncestor_iff.mp present

example (order : VerifiedOrder graph root) (found : graph.findNode? root = some node)
    (declared : constraint ∈ node.parentOrders) : constraint.Sublist order.output :=
  order.local_order found declared

example (order : VerifiedOrder graph root) (query : String)
    (present : order.indexAncestors.isAncestor query = true)
    (found : graph.findNode? query = some node) (declared : constraint ∈ node.parentOrders) :
    constraint.Sublist order.output :=
  order.ancestor_local_order (order.indexAncestors.isAncestor_iff.mp present) found declared

example (order : VerifiedOrder graph root)
    (ancestorOrder : VerifiedOrder graph ancestor) (path : Ancestor graph ancestor root)
    (before : ancestorOrder.precedes left right = true) : order.precedes left right = true :=
  order.monotone_precedes ancestorOrder path before

example (order : VerifiedOrder graph root) (reachable : Ancestor graph node root)
    (path : Ancestor graph base node) (different : base ≠ node) :
    order.precedes node base = true := order.inheritance_precedes reachable path different

example (order : VerifiedOrder graph root) (path : Ancestor graph node.name root)
    (found : graph.findNode? node.name = some node) (declared : constraint ∈ node.parentOrders)
    (before : Precedes constraint left right) : order.precedes left right = true :=
  order.local_precedes path found declared before

example (order : VerifiedOrder graph root) (accepted : order.precedes left right = true) :
    Ancestor graph left root ∧ Ancestor graph right root := order.precedes_members accepted

example (order : VerifiedOrder graph root) (rename : String → String)
    (injective : Function.Injective rename) (unique : (graph.nodes.map Node.name).Nodup) :
    VerifiedOrder (graph.rename rename) (rename root) := order.rename rename injective unique

example (order : VerifiedOrder graph root) (rename : String → String)
    (injective : Function.Injective rename) (unique : (graph.nodes.map Node.name).Nodup) :
    (order.rename rename injective unique).precedes (rename left) (rename right) =
      order.precedes left right := order.rename_precedes rename injective unique

example (receipt : LinearizeState.AuditedNode table node)
    (valid : LinearizeState.MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node) :
    GraphTrace graph node.name receipt.result.precedence
      (if node.suffix then receipt.result.precedence else
        LinearizeState.selectedTail table receipt.result.inheritedSuffix) :=
  receipt.graphSound valid found

example (current : ProofObject Key Value) (update : Patch Key Value)
    (certificate : Certificate current) (obligation : Obligation Key Value)
    (owned : obligation ∈ current.obligations) (safe : unaffected obligation update) :
    obligation.holds (append current update).state :=
  reuse current update certificate obligation owned safe

example (current : ProofObject Key Value) (update : Patch Key Value)
    (certificate : Certificate current)
    (affected : ∀ obligation, obligation ∈ current.obligations →
      ¬ unaffected obligation update → obligation.holds (append current update).state)
    (added : ∀ obligation, obligation ∈ update.obligations →
      obligation.holds (append current update).state) : Certificate (append current update) :=
  close current update certificate affected added

example [DecidableEq Key] (earlier : List (Sigma Value))
    (key : Key) (value : Value key) (state : State Key Value) :
    (Patch.setMany (earlier ++ [⟨key, value⟩])).apply state key = value :=
  Patch.setMany_last earlier key value state

#eval IO.println "REUSABLE-CONTRACTS-OK"
end LeanPoo.Tests.ReusableContracts
