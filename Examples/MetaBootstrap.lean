import LeanPoo.Prototype.MetaBootstrap
import LeanPoo.Functional.NonlocalDeclarations

/-! Self-description at a constant base and nonlocal declaration publication.
Native function/getter execution and exception effects have separate Gerbil tests;
these examples prove the pure hook/metadata/order/publication boundaries. -/
namespace LeanPoo.Examples.MetaBootstrap
open Prototype.MetaPrototype Functional.InheritedMOP Functional.DeclarativeMetadata
open Prototype Prototype.DescriptorReflection
/-- A root interprets extension metadata with a visible transformation. -/
def root : Bootstrap Unit String String Nat :=
  ⟨identityHook, fun _ next _ => (next ()).map (· + 1)⟩
/-- Arbitrarily refusing ordinary sources cannot prevent anchor self-description. -/
example : bootstrapReflect root () (fun _ => .error "not available") = .ok root :=
  bootstrapReflect_fixed _ _ _
/-- A root's extension metadata is still interpreted by its own compiler. -/
example : bootstrapLookup root () (fun _ => .ok 7) (.field "level") = .ok 8 := rfl
/-- The constant base does not suppress refusal on an ordinary field. -/
example : bootstrapLookup root () (fun _ => .error "source refused") (.field "level") =
    .error "source refused" := rfl
/-- Metadata of one property; descriptor laws reuse the existing admission layer. -/
def publicAmount : SlotDeclaration Nat := ⟨(Descriptor.top "Nat" toString).refine "Amount" (· ≤ 30), false⟩
/-- A private context annotation is never exposed in the public name catalog. -/
def privateRevision : SlotDeclaration Nat := {publicAmount with hidden := true}
/-- A nonlocal fragment contributes multiple metadata rows at the current context.
The getter row here is metadata only; native getter bodies are tested separately. -/
def property : Expansion (Nat × Bool) Nat := fun _ =>
  .ok [("amount",publicAmount),("read-amount",publicAmount),("amount-revision",privateRevision)]
/-- An approval is recomputed from this context before selecting later fragments. -/
def approval : Expansion (Nat × Bool) Nat := fun context =>
  if context.2 then .ok [] else .error "service declaration refused"
/-- Existing fragments compose through a common Reader context and one finalizer. -/
def candidate (context : Nat × Bool) : Except String (Catalog Nat) :=
  elaborate [approval,property] context (fun _ entries => .ok entries)
/-- Successful publication exposes exactly the generated public and private names. -/
example : (candidate (1,true)).map (fun catalog => (catalog.publicNames,catalog.privateNames)) =
    .ok (["amount","read-amount"],["amount-revision"]) := rfl
/-- Refusal blocks the whole remaining suffix and never produces a partial catalog. -/
example : candidate (2,false) = .error "service declaration refused" := rfl
/-- The previous publication survives refusal; recovery uses current context. -/
example (old : Catalog Nat) : publishDeclarations old (candidate (2,false)) = old := rfl
/-- A finalizer cannot smuggle a duplicate name past declaration validation. -/
example : elaborate [property] (3,true) (fun _ entries => .ok (entries ++ [("amount",publicAmount)])) =
    .error "duplicate or reserved declaration name" := rfl
/-- User expansion cannot shadow the nonlocal catalog protocol fields. -/
example : elaborate ([] : List (Expansion Unit Nat)) ()
    (fun _ _ => .ok [(".public-slots",publicAmount)]) =
    .error "duplicate or reserved declaration name" := rfl
/-- One expansion callback can depend on the current context without caching it. -/
def current : Expansion Nat Nat := fun revision =>
  if revision = 3 then .ok [("current",publicAmount)] else .error "revision refused"
/-- Reuse of the same action does not retain a previous admission. -/
example : [expandForms [current] 3, expandForms [current] 2, expandForms [current] 3] =
    [.ok [("current",publicAmount)], .error "revision refused", .ok [("current",publicAmount)]] := rfl
#print axioms bootstrapLookup_order
#print axioms bootstrapLookup_slot
#print axioms bootstrapLookup_field
#print axioms bootstrapReflect_fixed
#print axioms expandForms_append
#print axioms expandForms_refused
#print axioms elaborate_source
#print axioms Catalog.names_valid
#print axioms publishDeclarations_refused
end LeanPoo.Examples.MetaBootstrap
