import LeanPoo.Examples.JointTopology
import LeanPoo.Functional.JointReceipts

/-! Shared certified receipt construction for actual component topology controls. -/
namespace LeanPoo.Examples.JointReceipts
open LeanPoo.Examples.JointTopology
/-- Receipt validity means actual local and whole-family checks succeeded. -/
abbrev Receipt := Functional.JointPublication.Approved (Revision := Nat) (fun state : State => approved state = true)
/-- Each installation supplies the guard revision observed for that receipt. -/
abbrev Attempt := Functional.JointPublication.Installation (Revision := Nat) (fun state : State => approved state = true)
/-- Mint only an actually admitted candidate, retaining a proof of that check. -/
def certify (expected : Nat) (state : State) (revision : Nat) : Except String Receipt :=
  if checked : approved state = true then .ok ⟨expected,state,revision,checked⟩ else .error "joint admission refused"
end LeanPoo.Examples.JointReceipts
