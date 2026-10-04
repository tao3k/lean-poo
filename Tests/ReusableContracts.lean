import LeanPoo.C4.VerifiedOrder
import LeanPoo.Proof.Reuse
import LeanPoo.Proof.Batch

/-! Generic client contracts mirrored in docs/reusable-contracts.org. These
check how consumers combine the public API, independently of a demo domain. -/
namespace LeanPoo.Tests.ReusableContracts
open C4 Proof

example (order : VerifiedOrder graph root) (query : String)
    (present : order.indexAncestors.isAncestor query = true) : Ancestor graph query root :=
  order.indexAncestors.isAncestor_iff.mp present

example (order : VerifiedOrder graph root) (found : graph.findNode? root = some node)
    (declared : constraint ∈ node.parentOrders) : constraint.Sublist order.output :=
  order.local_order found declared

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
