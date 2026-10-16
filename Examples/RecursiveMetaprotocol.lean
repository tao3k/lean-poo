import LeanPoo.Prototype.RecursiveMetaprotocol
import LeanPoo.Functional.RecursiveDeclarations

/-! Matching pure controls for recursive metalevel feedback and shared forward
declarations. Native getter execution and mutable-source guards have Gerbil tests. -/
namespace LeanPoo.Examples.RecursiveMetaprotocol
open Prototype Prototype.MetaPrototype Functional.PositiveEquations
open Functional.DeclarativeMetadata Prototype.DescriptorReflection
/-- Two recursive metalevel facts need a grounded seed to become true. -/
def equations (seed : Bool) : Equations 3 := fun index =>
  match index.val with
  | 0 => .literal seed
  | 1 => .either (.read 0) (.read 2)
  | _ => .read 1
/-- The closed metadata selects one ordinary hook kernel. -/
def cook (facts : Bits 3) : Bootstrap Unit String String Nat :=
  ⟨Functional.InheritedMOP.identityHook,
    fun _ next _ => (next ()).map (fun value => value + if facts 2 then 1 else 0)⟩
/-- Grounded metadata propagates through both recursive components. -/
theorem enabled : (closePositive (equations true) cook).facts 2 = true := by
  have fixed := closePositive_fixed (equations true) cook
  have seed := congrFun fixed 0
  have first := congrFun fixed 1
  have second := congrFun fixed 2
  simp [step, equations, Expr.eval] at seed first second
  simp_all
/-- Removing the seed revokes the cycle, even though all-true is also a fixed point. -/
example : (closePositive (equations false) cook).facts 2 = false := by
  have fixed : step (equations false) (fun _ => false) = (fun _ => false) := by
    funext index
    obtain ⟨i, bound⟩ := index
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  have lower := closePositive_least (equations false) cook (fun _ => false) fixed 2
  cases value : (closePositive (equations false) cook).facts 2
  · rfl
  · exact False.elim (Bool.noConfusion (lower value))
/-- The same closed facts control non-anchor metadata interpretation. -/
example : bootstrapLookup (closePositive (equations true) cook).kernel ()
    (fun _ => .ok 7) (.field "level") = .ok 8 := by
  change Except.ok (ε := String) (7 + if (closePositive (equations true) cook).facts 2 then 1 else 0 : Nat) = .ok 8
  simp [enabled]
/-- Public and private descriptors reuse the existing declaration/admission model. -/
def publicSlot : SlotDeclaration Nat := ⟨Descriptor.top "Nat" toString, false⟩
/-- Revision metadata remains private in every generated branch. -/
def privateSlot : SlotDeclaration Nat := {publicSlot with hidden := true}
/-- Branches request shared leaves explicitly, even though the leaves are declared
later. Recursive continuations manipulate metadata, not arbitrary native closures. -/
def branch (name : String) : Recursive.Interaction String (Entries Nat) (Entries Nat) :=
  .call "limit" (fun limit => .call "revision" (fun revision =>
    .value (limit.map (fun row => (name,row.2)) ++ revision.map (fun row => (name ++ "-revision",row.2)))))
/-- One immutable current context/program owns memoized shared subrequests. -/
def program (approved : Bool) : Recursive.Generator String (Entries Nat) := fun key =>
  match key with
  | "family" => if approved then
      .call "billing" (fun billing => .call "risk" (fun risk => .value (billing ++ risk)))
    else .error "current approval refused"
  | "billing" => branch "billing"
  | "risk" => branch "risk"
  | "limit" => .value [("limit",publicSlot)]
  | "revision" => .value [("revision",privateSlot)]
  | _ => .error "unknown recursive declaration fragment"
/-- A whole-object finalizer can contribute metadata after all forward references. -/
def finalize (_ : Unit) (entries : Entries Nat) : Except String (Entries Nat) :=
  .ok (entries ++ [("total",publicSlot)])
/-- Source names expose exact complete root order without equating function fields. -/
def names (approved : Bool) : Except (ExpansionFailure String) (List String × Nat) := do
  let (resolved, cache) ← collectRecursive (program approved) 100 {} ["family"]
  return (resolved.entries.map Prod.fst, cache.statistics.hits)
/-- Source unfolding produces the complete ordered family. Native controls check
the two memo hits; universal receipt provenance is proved by Resolved.sources. -/
example : Recursive.solve (program true) 3 "family" =
    .value [("billing",publicSlot),("billing-revision",privateSlot),
      ("risk",publicSlot),("risk-revision",privateSlot)] := rfl
/-- Current approval refusal produces no partially expanded family. -/
example : names false = .error (.source "current approval refused") := rfl
/-- An explicit request cycle remains a machine diagnostic, not a meta fixed point. -/
def cycle : Recursive.Generator String (Entries Nat) := fun key => .call key .value
/-- Only positive metadata equations use least closure; cyclic expansion refuses. -/
example : (collectRecursive cycle 20 {} ["loop"]).map (fun _ => ()) =
    .error (.machine (.cycle ["loop","loop"])) := rfl
/-- Whole-object finalization uses the exact resolved expansion, with valid catalogs. -/
example (resolved : Resolved (program true) ["family"]) (catalog : Catalog Nat)
    (accepted : finishRecursive resolved () finalize = .ok catalog) :
    finalize () resolved.entries = .ok catalog.entries := finishRecursive_source _ _ _ _ accepted
#print axioms closePositive_fixed
#print axioms closePositive_least
#print axioms closePositive_cooked
#print axioms closePositive_reflect
#print axioms closePositive_bound
#print axioms Resolved.sources
#print axioms finishRecursive_source
#print axioms elaborateRecursive_source
#print axioms publishRecursive_refused
end LeanPoo.Examples.RecursiveMetaprotocol
