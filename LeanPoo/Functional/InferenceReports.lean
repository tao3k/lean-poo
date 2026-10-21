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

/-- Public Type operations consume one faithfully captured input, even when live
admission returns changed caller state. Scheme owns every operand BEFORE invoking
admission; this conditional model does not prove its heap copier or callbacks. -/
def withCapturedInputs (inputs : Input) (inspect : Input → Except Cause Buffer)
    (consume : Input → Except Cause Result) : Except Cause (Result × Buffer) :=
  (inspect inputs).bind fun after => (consume inputs).map fun result => (result, after)

/-- Caller edits remain observable, but cannot replace the admitted operands. -/
theorem withCapturedInputs_fresh (inputs : Input) (inspect : Input → Except Cause Buffer)
    (consume : Input → Except Cause Result) (after result)
    (inspected : inspect inputs = .ok after) (consumed : consume inputs = .ok result) :
    withCapturedInputs inputs inspect consume = .ok (result, after) := by
  simp [withCapturedInputs, inspected, consumed, Except.bind, Except.map]

/-- Original admission failures take precedence over any later consumer result. -/
theorem withCapturedInputs_error (inputs : Input) (inspect : Input → Except Cause Buffer)
    (consume : Input → Except Cause Result) (cause)
    (failed : inspect inputs = .error cause) :
    withCapturedInputs inputs inspect consume = .error cause := by
  simp [withCapturedInputs, failed, Except.bind]

/-- Compilation/check failures retain their exact cause after successful admission. -/
theorem withCapturedInputs_consume_error (inputs : Input) (inspect : Input → Except Cause Buffer)
    (consume : Input → Except Cause Result) (after cause)
    (inspected : inspect inputs = .ok after) (failed : consume inputs = .error cause) :
    withCapturedInputs inputs inspect consume = .error cause := by
  simp [withCapturedInputs, inspected, failed, Except.bind, Except.map]

/-- A successful result came from BOTH operations on the original captured input,
never a caller buffer returned by admission. This composes arbitrary existing
compiler/declaration laws without treating the changed buffer as a certificate. -/
theorem withCapturedInputs_sound (inputs : Input) (inspect : Input → Except Cause Buffer)
    (consume : Input → Except Cause Result) (after result)
    (accepted : withCapturedInputs inputs inspect consume = .ok (result, after)) :
    inspect inputs = .ok after ∧ consume inputs = .ok result := by
  cases first : inspect inputs with
  | error cause => simp [withCapturedInputs, first, Except.bind] at accepted
  | ok observed =>
    cases second : consume inputs with
    | error cause => simp [withCapturedInputs, first, second, Except.bind, Except.map] at accepted
    | ok value =>
      have same : (value, observed) = (result, after) := by
        simpa [withCapturedInputs, first, second, Except.bind, Except.map] using accepted
      cases same
      exact ⟨rfl, rfl⟩

/-- Captured binary judgments retain the existing universal subtype proof for
BOTH original operands, regardless of the caller state produced by admission. -/
theorem withCapturedInputs_subtype (fuel : Nat) (source target : Ty)
    (inspect : Ty × Ty → Except Cause Buffer) (after)
    (accepted : withCapturedInputs (source, target) inspect
      (fun pair => .ok (check fuel pair.1 pair.2)) = .ok (true, after)) :
    Subtype source target := by
  have current := (withCapturedInputs_sound _ _ _ _ _ accepted).2
  exact check_sound fuel source target (Except.ok.inj current)

/-- Finish any Type result using the EXISTING source admission. Snapshot models
actual post-consumer source observations, including unused candidates/queries.
Host recording, source identity and revision fidelity are explicit premises. -/
def finishTypeRequest [DecidableEq Descriptor]
    (sources : List (Parameters.BoundParameter Name Descriptor))
    (run : Unit → Except Cause (Result × Snapshot))
    (fields : Snapshot → Name → Option Descriptor) (revision : Snapshot → Descriptor → Nat) :
    Except (PrototypeTypes.Failure ⊕ Cause) Result :=
  ((run ()).mapError Sum.inr).bind fun pair =>
    (admitDeclaredBindings sources (fields pair.2) (revision pair.2) pair.1).mapError Sum.inl

/-- Original callback/refusal causes precede all success-only source checks. -/
theorem finishTypeRequest_error [DecidableEq Descriptor] (sources) (run : Unit → Except Cause (Result × Snapshot))
    (fields : Snapshot → Name → Option Descriptor) revision cause
    (failed : run () = .error cause) :
    finishTypeRequest sources run fields revision = .error (.inr cause) := by
  simp [finishTypeRequest, failed, Except.mapError, Except.bind]

/-- Even false, no-solution or ambiguous successful results require current sources. -/
theorem finishTypeRequest_stale [DecidableEq Descriptor] (sources)
    (run : Unit → Except Cause (Result × Snapshot)) (fields : Snapshot → Name → Option Descriptor)
    revision result after (completed : run () = .ok (result, after))
    (stale : Parameters.bindingsCurrent sources (fields after) (revision after) = false) :
    finishTypeRequest sources run fields revision = .error (.inl .bounds) := by
  simp [finishTypeRequest, completed, admitDeclaredBindings, stale, Except.mapError, Except.bind]

/-- A healthy completed operation returns its exact result, without re-solving. -/
theorem finishTypeRequest_fresh [DecidableEq Descriptor] (sources)
    (run : Unit → Except Cause (Result × Snapshot)) (fields : Snapshot → Name → Option Descriptor)
    revision result after (completed : run () = .ok (result, after))
    (current : Parameters.bindingsCurrent sources (fields after) (revision after) = true) :
    finishTypeRequest sources run fields revision = .ok result := by
  simp [finishTypeRequest, completed, admitDeclaredBindings, current, Except.mapError, Except.bind]

/-- Every published result comes from the original consumer with a jointly
current final source set. No result classification can bypass the source gate. -/
theorem finishTypeRequest_sound [DecidableEq Descriptor] (sources)
    (run : Unit → Except Cause (Result × Snapshot)) (fields : Snapshot → Name → Option Descriptor)
    revision result (accepted : finishTypeRequest sources run fields revision = .ok result) :
    ∃ after, run () = .ok (result, after) ∧
      Parameters.bindingsCurrent sources (fields after) (revision after) = true := by
  cases completed : run () with
  | error cause => simp [finishTypeRequest, completed, Except.mapError, Except.bind] at accepted
  | ok pair =>
    rcases pair with ⟨value, after⟩
    by_cases current : Parameters.bindingsCurrent sources (fields after) (revision after) = true
    · have same : value = result := by
        simpa [finishTypeRequest, completed, admitDeclaredBindings, current, Except.mapError, Except.bind] using accepted
      subst value
      exact ⟨after, rfl, current⟩
    · simp [finishTypeRequest, completed, admitDeclaredBindings, current, Except.mapError, Except.bind] at accepted

/-- Universal currentness of EACH recorded source follows from the final gate,
including sources omitted from the selected signature or bound receiver. -/
theorem finishTypeRequest_sources [DecidableEq Descriptor] (sources)
    (run : Unit → Except Cause (Result × Snapshot)) (fields : Snapshot → Name → Option Descriptor)
    revision result (accepted : finishTypeRequest sources run fields revision = .ok result) :
    ∃ after, run () = .ok (result, after) ∧
      ∀ source ∈ sources, fields after source.name = some source.descriptor ∧
        revision after source.descriptor = source.revision := by
  obtain ⟨after, completed, current⟩ := finishTypeRequest_sound sources run fields revision result accepted
  exact ⟨after, completed, fun source member =>
    Parameters.bindingsCurrent_sound sources (fields after) (revision after) current source member⟩

end LeanPoo.Functional.DeclarativeMetadata
