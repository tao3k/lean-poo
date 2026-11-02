import LeanPoo.Functional.InheritanceHooks

/-! An explicit constant base terminates MOP self-description. The two inherited
operation anchors remain reflected metadata; other metadata uses the slot hook.
This advances future work, without asserting an unrestricted recursive knot. -/
namespace LeanPoo.Prototype.MetaPrototype
open Functional.InheritedMOP
/-- Compilation keeps the inherited source delayed and the current receiver explicit. -/
abbrev SlotHook (Context Key α : Type) :=
  Context → (Unit → Except String α) → Key → Except String α
/-- A captured version of the two operations at the terminating metalevel base. -/
structure Bootstrap (Context Key Name α : Type) where
  computeOrder : Hook Context (List Name)
  computeSlot : SlotHook Context Key α
/-- Reserved operation fields and ordinary extension metadata share one typed view. -/
inductive BootstrapField (Key : Type) where
  | computeOrder | computeSlot | field (key : Key)
/-- Unlike ordinary metadata, anchors are functions used to interpret metadata. -/
abbrev BootstrapValue (Context Key Name α : Type) : BootstrapField Key → Type
  | .computeOrder => Hook Context (List Name)
  | .computeSlot => SlotHook Context Key α
  | .field _ => α
/-- Read anchors from the constant base. Reading another field is interpreted by
that SAME captured slot hook, so self-description needs no unbounded meta lookup. -/
def bootstrapLookup (root : Bootstrap Context Key Name α) (self : Context)
    (source : Key → Except String α) : (field : BootstrapField Key) →
    Except String (BootstrapValue Context Key Name α field)
  | .computeOrder => .ok root.computeOrder
  | .computeSlot => .ok root.computeSlot
  | .field key => root.computeSlot self (fun _ => source key) key
/-- Anchor reads do not invoke a source, even if every ordinary field would refuse. -/
theorem bootstrapLookup_order (root : Bootstrap Context Key Name α) (self : Context) (source : Key → Except String α) :
    bootstrapLookup root self source .computeOrder = .ok root.computeOrder := rfl
/-- The slot compiler reflected by the root is the very compiler interpreting it. -/
theorem bootstrapLookup_slot (root : Bootstrap Context Key Name α) (self : Context) (source : Key → Except String α) :
    bootstrapLookup root self source .computeSlot = .ok root.computeSlot := rfl
/-- The constant base does not bypass the hook on extension metadata. -/
theorem bootstrapLookup_field (root : Bootstrap Context Key Name α) (self : Context) (source : Key → Except String α) (key : Key) :
    bootstrapLookup root self source (.field key) = root.computeSlot self (fun _ => source key) key := rfl
/-- Reify the MOP root using the same reflected metadata operations. -/
def bootstrapReflect (root : Bootstrap Context Key Name α) (self : Context) (source : Key → Except String α) :
    Except String (Bootstrap Context Key Name α) := do
  let order ← bootstrapLookup root self source .computeOrder
  let slot ← bootstrapLookup root self source .computeSlot
  return ⟨order, slot⟩
/-- Self-description closes exactly at the supplied base, for EVERY source and
receiver. This proves anchor reflection, not termination/equivalence of callbacks. -/
theorem bootstrapReflect_fixed (root : Bootstrap Context Key Name α) (self : Context) (source : Key → Except String α) :
    bootstrapReflect root self source = .ok root := by cases root; rfl
end LeanPoo.Prototype.MetaPrototype
