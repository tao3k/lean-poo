import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.RawArguments
import LeanPoo.Functional.VariantValidation

/-! Realizable raw-argument paths and complete declaration publication. These
examples retain the original metadata while checking a private pruned graph. -/
namespace LeanPoo.Examples.TypedMethodDeclarations
open LeanPoo.Functional LeanPoo.Functional.FunctionSignature LeanPoo.Functional.DeclarativeMetadata

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

/-- A finite intrinsic interpretation distinguishes keyword, rest marker, void
and false. True is deliberately outside the optional token-valued contract. -/
def tokenClassMember (kind : Nat) (token : ArgumentToken String (Option Bool)) : Bool :=
  match kind, token with
  | 0, .keyword _ | 1, .restEscape | 2, .value none | 3, .value (some false) => true
  | _, _ => false
/-- Origin two models OrFalse(Maybe(Or Keyword rest-marker)); origin three
stands for a wrapping child and cannot acquire an intrinsic identity view. -/
def tokenOriginView : Nat → Except String (List Nat)
  | 0 => .ok [0]
  | 1 => .ok [1]
  | 2 => .ok [3, 2, 0, 1]
  | _ => .error "wrapping origin"
/-- Original membership is interpreted independently of the private view. Its
host correspondence is limited to these intrinsic token classes, not Functions. -/
def tokenOriginMember (origin : Nat) (token : ArgumentToken String (Option Bool)) : Bool :=
  match origin, token with
  | 0, .keyword _ | 1, .restEscape => true
  | 2, .keyword _ | 2, .restEscape | 2, .value none | 2, .value (some false) => true
  | _, _ => false

/-- Complete child interpretation holds for every key and value in this model,
including false/void and both escape controls, without sampled coverage. -/
theorem tokenOriginView_law (origin views) (projected : tokenOriginView origin = .ok views)
    (value : ArgumentToken String (Option Bool)) :
    tokenOriginMember origin value = views.any (fun kind => tokenClassMember kind value) := by
  match origin with
  | 0 | 1 | 2 =>
    simp only [tokenOriginView, Except.ok.injEq] at projected
    subst views
    cases value with
    | value data => cases data with
      | none => rfl
      | some bit => cases bit <;> rfl
    | keyword key => rfl
    | keyEscape => rfl
    | restEscape => rfl
  | _ + 3 => simp [tokenOriginView] at projected

/-- Complete unique inference publishes the original optional origin metadata;
the private view is a coverage artifact and never replaces that declaration. -/
def inferredTokenOrigins := inferDeclared 2
  (fun bad => !bad && (Validation.traverse tokenOriginView [2]).isOk)
  [true, false] (fun bad => (Except.ok (bad, [2]) : Except String (Bool × List Nat)))

example : Validation.traverse tokenOriginView [0, 1, 2] = .ok [[0], [1], [3, 2, 0, 1]] := rfl
example : Validation.traverse tokenOriginView [0, 3, 2] = .error "wrapping origin" := rfl
#guard match inferredTokenOrigins with
  | .ok (.unique false, some (false, [2])) => true
  | _ => false
#guard !tokenOriginMember 2 (.value (some true))
#guard tokenOriginMember 2 (.value (some false)) && tokenOriginMember 2 (.value none)

/-- Ordered identity validation of the complete view returns the same original
value after publication. No wrapper/opaque leaf or host effect is certified. -/
theorem inferredTokenOrigins_identity (bad artifact)
    (published : inferredTokenOrigins = .ok (.unique bad, some artifact))
    (value : ArgumentToken String (Option Bool)) (admitted : tokenOriginMember 2 value = true) :
    artifact = (bad, [2]) ∧
    LeanPoo.Functional.VariantValidation.union
      (fun branch token => branch.any (fun kind => tokenClassMember kind token))
      (fun branch token => branch.any (fun kind => tokenClassMember kind token))
      (fun _ token => (Except.ok token : Except String _))
      "missing" "invalid" [[3, 2, 0, 1]] value = .ok value := by
  obtain ⟨_, _, built⟩ := inferDeclared_unique 2 _ [true, false] _ published
  refine ⟨(Except.ok.inj built).symm, ?_⟩
  apply LeanPoo.Functional.VariantValidation.union_identity
  · have same := rawOriginView_membership tokenOriginView tokenOriginMember
      (fun branch token => branch.any (fun kind => tokenClassMember kind token))
      tokenOriginView_law [2] [[3, 2, 0, 1]] rfl value
    simpa [admitted] using same.symm
  · intro _ _ _; rfl

#print axioms rawOriginView_noPartial
#print axioms rawOriginView_order
#print axioms rawOriginView_membership
#print axioms rawOriginView_ordinary
#print axioms tokenOriginView_law
#print axioms inferredTokenOrigins_identity

end LeanPoo.Examples.TypedMethodDeclarations
