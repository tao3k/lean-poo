import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.RawArguments

/-! Realizable raw-argument paths and complete declaration publication. These
examples retain the original metadata while checking a private pruned graph. -/
namespace LeanPoo.Examples.TypedMethodDeclarations
open LeanPoo.Functional.FunctionSignature LeanPoo.Functional.DeclarativeMetadata

/-- Origin zero denotes an impossible retired payload; one denotes live numeric
data. The second edge keeps the retired keyword and payload in the original
metadata, while the remaining loop permits arbitrarily long live rest traces. -/
def retiredOriginsGraph : List (RawTransition Nat Nat) :=
  [⟨0, 1, [1]⟩, ⟨0, 1, [2, 0]⟩, ⟨1, 1, [1]⟩, ⟨1, 2, []⟩]
/-- A positive witness is separate from missing admission evidence. Rejecting
origin two alone must never justify removing its entire potentially live edge. -/
def retiredOriginEmpty (origin : Nat) : Bool := decide (origin = 0)
/-- Use the existing complete declaration search; its builder retains the
original graph. Pruning only prepares the private call-coverage graph. -/
def inferredRetiredOrigins := inferDeclared 2
  (fun bad => rawGraphCheck 2 (rawPruneEdges retiredOriginEmpty retiredOriginsGraph)
    [2] 0 true (fun _ origin => decide (origin = 1) && !bad))
  [true, false] (fun bad => (Except.ok (bad, retiredOriginsGraph) : Except String (Bool × List (RawTransition Nat Nat))))

#guard (rawPruneEdges retiredOriginEmpty retiredOriginsGraph).length == 3
#guard !rawGraphCheck 2 retiredOriginsGraph [2] 0 true (fun _ origin => decide (origin = 1))
#guard rawGraphCheck 2 (rawPruneEdges retiredOriginEmpty retiredOriginsGraph) [2] 0 true
  (fun _ origin => decide (origin = 1))
#guard !rawGraphCheck 2 (rawPruneEdges retiredOriginEmpty retiredOriginsGraph) [2] 0 false
  (fun _ origin => decide (origin = 1))
#guard !rawGraphCheck 0 (rawPruneEdges retiredOriginEmpty retiredOriginsGraph) [2] 0 true
  (fun _ origin => decide (origin = 1))
#guard match inferredRetiredOrigins with
  | .ok (.unique false, some (false, graph)) => graph.length == 4
  | _ => false

/-- All realizable original traces of the uniquely inferred callback retain
their slot evidence. Child-witness soundness and actual trace realizability are
explicit: neither a sampled absence nor a visited cycle can stand in for them. -/
theorem inferredRetiredOrigins_sound (bad artifact)
    (published : inferredRetiredOrigins = .ok (.unique bad, some artifact))
    (trace : List (RawTransition Nat Nat)) (path : RawGraphPath retiredOriginsGraph 0 2 trace)
    (realized : ∀ edge ∈ trace, ∀ origin ∈ edge.origins, ∃ value : Nat, origin ≠ 0 ∧ value = origin) :
    artifact = (bad, retiredOriginsGraph) ∧
    trace.all (fun edge => edge.origins.all (fun origin => decide (origin = 1) && !bad)) = true := by
  obtain ⟨_, valid, built⟩ := inferDeclared_unique 2 _ [true, false] _ published
  refine ⟨(Except.ok.inj built).symm, ?_⟩
  exact (rawGraphCheck_pruned_sound retiredOriginEmpty
    (fun origin (value : Nat) => origin ≠ 0 ∧ value = origin)
    (by intro origin empty value member; exact member.1 (of_decide_eq_true empty))
    2 retiredOriginsGraph [2] 0 true _ valid path (by simp) realized).2

#print axioms rawPruneEdges_mem
#print axioms rawGraphPath_prune
#print axioms rawGraphCheck_pruned_sound
#print axioms inferredRetiredOrigins_sound

end LeanPoo.Examples.TypedMethodDeclarations
