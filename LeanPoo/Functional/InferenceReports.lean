import LeanPoo.Functional.MethodDeclarations

/-! Request-owned inference diagnostics compose the existing complete declaration
solver. Lean lists represent faithfully captured Scheme syntax. The callback may
return arbitrary changed caller state; it cannot replace the captured queries.
Host copying, source admission, metering and mutable execution have Gerbil tests;
this module proves neither a host heap implementation nor unrestricted inference. -/
namespace LeanPoo.Functional.DeclarativeMetadata
open PrototypeTypes

/-- Project the existing declaration result with its original query snapshot.
The builder's second result models caller state after its effects; those effects
are not rolled back, and that state is not substituted for the solve evidence. -/
def inferDeclaredQueries (fuel budget : Nat) (bounds queries : List (Expr × Expr))
    (candidates : List (Nat → Ty))
    (build : (Nat → Ty) → Except Error (Artifact × Buffer)) :
    Except (PrototypeTypes.Failure ⊕ Error) ((Inference (Nat → Ty) × Option Artifact) × List (Expr × Expr)) :=
  (inferDeclared budget (satisfies fuel (bounds ++ queries)) candidates
    (fun env => (build env).map Prod.fst)).map (fun result => (result, queries))

/-- A unique solve reports its captured constraints, irrespective of the new
caller state returned by a successful declaration builder. -/
theorem inferDeclaredQueries_unique (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer)) (env artifact after)
    (completed : inferBounded budget (satisfies fuel (bounds ++ queries)) candidates = .ok (.unique env))
    (built : build env = .ok (artifact, after)) :
    inferDeclaredQueries fuel budget bounds queries candidates build =
      .ok ((.unique env, some artifact), queries) := by
  simp [inferDeclaredQueries, inferDeclared, completed, built, Except.map]

/-- No-solution diagnostics retain the captured batch without calling a builder. -/
theorem inferDeclaredQueries_none (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer))
    (completed : inferBounded budget (satisfies fuel (bounds ++ queries)) candidates = .ok .none) :
    inferDeclaredQueries fuel budget bounds queries candidates build = .ok ((.none, none), queries) := by
  simp [inferDeclaredQueries, inferDeclared, completed, Except.map]

/-- Ambiguous diagnostics keep all assignments and never initialize a declaration. -/
theorem inferDeclaredQueries_ambiguous (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer)) (assignments)
    (completed : inferBounded budget (satisfies fuel (bounds ++ queries)) candidates = .ok (.ambiguous assignments)) :
    inferDeclaredQueries fuel budget bounds queries candidates build = .ok ((.ambiguous assignments, none), queries) := by
  simp [inferDeclaredQueries, inferDeclared, completed, Except.map]

/-- The original complete search and builder supply every published artifact;
all reported inequalities, together with the original bounds, are derivable. -/
theorem inferDeclaredQueries_sound (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer)) (env artifact reported)
    (accepted : inferDeclaredQueries fuel budget bounds queries candidates build =
      .ok ((.unique env, some artifact), reported)) :
    reported = queries ∧ env ∈ candidates ∧
      (∀ a b, (a, b) ∈ bounds ++ reported → Subtype (substitute env a) (substitute env b)) ∧
      ∃ after, build env = .ok (artifact, after) := by
  unfold inferDeclaredQueries at accepted
  cases outcome : inferDeclared budget (satisfies fuel (bounds ++ queries)) candidates
      (fun env => (build env).map Prod.fst) with
  | error cause =>
    rw [outcome] at accepted
    cases accepted
  | ok result =>
    rw [outcome] at accepted
    have same : (result, queries) = ((.unique env, some artifact), reported) := by
      simpa only [Except.map, Except.ok.injEq] using accepted
    have captured : queries = reported := congrArg Prod.snd same
    have installed : result = (.unique env, some artifact) := congrArg Prod.fst same
    rw [installed] at outcome
    obtain ⟨member, valid, projected⟩ := inferDeclared_unique _ _ _ _ outcome
    subst reported
    refine ⟨rfl, member, fun a b constraint => satisfies_sound _ _ _ valid constraint, ?_⟩
    cases built : build env with
    | error cause => simp [built, Except.map] at projected
    | ok value =>
      obtain ⟨actual, after⟩ := value
      have first : actual = artifact := by simpa only [built, Except.map, Except.ok.injEq] using projected
      subst actual
      exact ⟨after, rfl⟩

/-- An incomplete scan cannot return even diagnostic success from a valid prefix. -/
theorem inferDeclaredQueries_exhausted (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer))
    (incomplete : budget < candidates.length) :
    inferDeclaredQueries fuel budget bounds queries candidates build = .error (.inl .exhausted) := by
  simp [inferDeclaredQueries, inferDeclared_exhausted _ _ _ _ incomplete, Except.map]

/-- Callback failure keeps its exact cause; no successful report is manufactured
from the captured queries or the caller's later scratch state. -/
theorem inferDeclaredQueries_error (fuel budget bounds queries candidates)
    (build : (Nat → Ty) → Except Error (Artifact × Buffer)) (env cause)
    (completed : inferBounded budget (satisfies fuel (bounds ++ queries)) candidates = .ok (.unique env))
    (failed : build env = .error cause) :
    inferDeclaredQueries fuel budget bounds queries candidates build = .error (.inr cause) := by
  simp [inferDeclaredQueries, inferDeclared, completed, failed, Except.map]

end LeanPoo.Functional.DeclarativeMetadata
