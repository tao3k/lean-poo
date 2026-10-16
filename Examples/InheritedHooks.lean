import LeanPoo.Functional.InheritanceHooks
import LeanPoo.Object.CacheInvalidation
import LeanPoo.Object.SlotReflection

/-! Concrete inherited hooks, shared-source revisions and public metadata.
These checked models advance future MOP work; native effects and weak-table GC
behavior have separate Gerbil controls, not kernel implementation proofs. -/
namespace LeanPoo.Examples.InheritedHooks
open Functional.InheritedMOP Object Prototype Prototype.DescriptorReflection
/-- A shared declaration, protocol and diamond hierarchy are all explicit sources. -/
def services : C4.Graph := ⟨[
  ⟨"metadata", [], false⟩, ⟨"protocol", [], false⟩,
  ⟨"root", [["metadata"]], false⟩,
  ⟨"billing", [["root", "protocol"]], false⟩,
  ⟨"risk", [["root", "protocol"]], false⟩,
  ⟨"join", [["billing", "risk"]], false⟩,
  ⟨"unrelated", [], false⟩]⟩
/-- Initial cached observations are deliberately present on every owner. -/
def cached : String → RevisionCache Nat := fun _ => ⟨4, some 10⟩
/-- Shared dependency invalidation clears the diamond once and preserves its frame. -/
example : ((invalidateCaches services ["metadata"] cached "join").derived,
    (invalidateCaches services ["metadata"] cached "join").revision,
    (invalidateCaches services ["metadata"] cached "unrelated").derived) =
    (none, 5, some 10) := by decide
/-- Protocol revisions reach both service branches and the shared join. -/
example : (invalidateCaches services ["protocol"] cached "billing").derived = none ∧
    (invalidateCaches services ["protocol"] cached "risk").derived = none ∧
    (invalidateCaches services ["protocol"] cached "join").derived = none := by decide
/-- An inherited wrapper can transform a slot result; composition keeps order. -/
def incrementHook : Hook Unit Nat := fun _ next => (next ()).map (· + 1)
/-- This is the explicit transformed semantics, not an assertion of identity. -/
example : composeHooks incrementHook incrementHook () (fun _ => .ok 10) = .ok 12 := rfl
/-- A normal order hook preserves the current reference order. -/
example : checkedOrder identityHook () (.ok ["join", "billing", "risk", "root"]) =
    .ok ["join", "billing", "risk", "root"] := rfl
/-- Arbitrary reordered ancestors cannot masquerade as checked C3. -/
example : checkedOrder (fun _ _ => .ok ["root", "join"]) () (.ok ["join", "root"]) =
    .error "inheritance hook must preserve checked C3 order" := rfl
/-- Source refusal precedes selection even when a hook could fabricate an order. -/
example : checkedOrder (Name := String) (fun _ _ => .ok ["fabricated"]) () (.error "cycle") =
    .error "cycle" := rfl
/-- Reuse the existing runtime descriptor refinement for declared natural slots. -/
def amount : SlotDeclaration Nat := ⟨(Descriptor.top "Nat" toString).refine "SmallAmount" (· ≤ 30), false⟩
/-- A private declaration uses the same descriptor but a different public surface. -/
def secret : SlotDeclaration Nat := {amount with hidden := true}
/-- Public inspection removes private metadata without demanding a value. -/
example : (publicSlots [("amount", amount), ("secret", secret)]).map Prod.fst = ["amount"] := rfl
/-- Public write refusal never calls its supplied edit, including a repairing edit. -/
example : writeSlot amount 40 (fun _ => .ok (10 : Nat)) =
    .error "value rejected by SmallAmount" := rfl
/-- Current metadata controls each call; an earlier accepted value is not approval. -/
example : [writeSlot amount 20 (fun n => .ok n), writeSlot secret 20 (fun n => .ok n),
    writeSlot amount 30 (fun n => .ok n)] =
    [.ok 20, .error "slot is hidden or undeclared", .ok 30] := rfl
/-- Sealing rejects the source edit and leaves the caller's retained publication. -/
example : publishEdit (10 : Nat) (guardedEdit true false 10 (fun _ => 20)) = 10 := rfl
#print axioms composeHooks_assoc
#print axioms checkedOrder_sound
#print axioms checkedOrder_error
#print axioms invalidateCaches_descendant
#print axioms invalidateCaches_once
#print axioms invalidateCaches_frame
#print axioms publishEdit_sealed
#print axioms publicSlots_visible
/-- A raw cached/default/hook value cannot bypass its current descriptor. -/
example : readSlot amount (fun _ => .ok 40) = .error "value rejected by SmallAmount" := rfl
#print axioms readSlot_hidden
#print axioms readSlot_valid
#print axioms writeSlot_rejected
#print axioms writeSlot_admitted
end LeanPoo.Examples.InheritedHooks
