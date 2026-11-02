import LeanPoo.Functional.NonlocalDeclarations
import LeanPoo.Prototype.RecursiveCache

/-! Safe recursive declaration fragments with forward/shared requests. The existing
memo evaluator owns every receipt. No diagnostic or source error can become an
accepted declaration prefix. This is generalized MOP future work. -/
namespace LeanPoo.Functional.DeclarativeMetadata
open Prototype Prototype.DescriptorReflection Prototype.Recursive
/-- One recursive result is a finite list of ordinary named slot declarations. -/
abbrev Entries (α : Type) := List (String × SlotDeclaration α)
/-- Machine diagnostics remain distinct from explicit source-language refusals. -/
inductive ExpansionFailure (Input : Type) where
  | machine (diagnostic : Cached.Diagnostic Input)
  | source (message : String)
/-- Each chunk is the completed source result of its exact root in source order. -/
inductive FragmentSources (program : Recursive.Generator Input (Entries α)) :
    List Input → List (Entries α) → Prop where
  | nil : FragmentSources program [] []
  | cons {key rest entries chunks} (head : Returns program key entries)
      (tail : FragmentSources program rest chunks) : FragmentSources program (key :: rest) (entries :: chunks)
/-- A complete ordered recursive expansion carries all of its source witnesses. -/
structure Resolved (program : Recursive.Generator Input (Entries α)) (roots : List Input) where
  chunks : List (Entries α)
  origin : FragmentSources program roots chunks
/-- Nonlocal finalization receives the whole ordered expansion, including all roots. -/
def Resolved.entries (resolved : Resolved (α := α) program roots) : Entries α := resolved.chunks.flatten
/-- Traverse roots using one owned memo; shared completed dependencies are reusable.
The cache never crosses the context/program boundary and failures return no prefix. -/
def collectRecursive [DecidableEq Input] (program : Recursive.Generator Input (Entries α))
    (budget : Nat) (cache : Cached.Cache program) (roots : List Input) :
    Except (ExpansionFailure Input) (Resolved program roots × Cached.Cache program) :=
  match roots with
  | [] => .ok (⟨[], .nil⟩, cache)
  | key :: rest =>
    match Cached.run program key budget cache with
    | .error diagnostic => .error (.machine diagnostic)
    | .ok (receipt, next) =>
      match result : receipt.result with
      | .error message => .error (.source message)
      | .value entries => do
        let (tail, final) ← collectRecursive program budget next rest
        have source : Returns program key entries := by
          obtain ⟨depth, observed⟩ := receipt.observed
          exact ⟨depth, by simpa [result, Cached.Completed.observation] using observed⟩
        return (⟨entries :: tail.chunks, .cons source tail.origin⟩, final)
/-- Every resolved root has its own actual finite source evaluation. -/
theorem Resolved.sources (resolved : Resolved program roots) :
    FragmentSources program roots resolved.chunks := resolved.origin
/-- Existing finalization and reserved-name admission apply unchanged after recursion. -/
def finishRecursive (resolved : Resolved (α := α) program roots) (context : Context)
    (finalize : Context → Entries α → Except String (Entries α)) : Except String (Catalog α) :=
  elaborate [fun _ => .ok resolved.entries] context finalize
/-- Success binds the final catalog to the COMPLETE recursively resolved source. -/
theorem finishRecursive_source (resolved : Resolved (α := α) program roots) (context : Context)
    (finalize : Context → Entries α → Except String (Entries α)) (catalog : Catalog α)
    (accepted : finishRecursive resolved context finalize = .ok catalog) :
    finalize context resolved.entries = .ok catalog.entries := by
  obtain ⟨entries, expanded, finalized⟩ := elaborate_source _ _ _ _ accepted
  simp [expandForms, bind, Except.bind, pure, Except.pure] at expanded
  subst entries
  exact finalized
/-- Recursive/source refusal and whole-catalog admission refusal stay distinct. -/
inductive RecursiveFailure (Input : Type) where
  | expansion (failure : ExpansionFailure Input)
  | finalization (message : String)
/-- Complete one current program's recursive expansion before finalizing/publishing.
No caller-provided memo can cross the immutable program/context boundary. -/
def elaborateRecursive [DecidableEq Input] (program : Recursive.Generator Input (Entries α))
    (roots : List Input) (budget : Nat) (context : Context)
    (finalize : Context → Entries α → Except String (Entries α)) :
    Except (RecursiveFailure Input) (Catalog α) :=
  match collectRecursive program budget {} roots with
  | .error failure => .error (.expansion failure)
  | .ok (resolved, _) => (finishRecursive resolved context finalize).mapError .finalization
/-- Every accepted final catalog comes from complete, source-certified root chunks
and the finalizer at this same current context. No partial prefix can be admitted. -/
theorem elaborateRecursive_source [DecidableEq Input] (program : Recursive.Generator Input (Entries α))
    (roots : List Input) (budget : Nat) (context : Context) (finalize) (catalog : Catalog α)
    (accepted : elaborateRecursive program roots budget context finalize = .ok catalog) :
    ∃ resolved : Resolved program roots, finalize context resolved.entries = .ok catalog.entries := by
  cases collected : collectRecursive program budget {} roots with
  | error failure => simp [elaborateRecursive, collected] at accepted
  | ok pair =>
    cases finished : finishRecursive pair.1 context finalize with
    | error message => simp [elaborateRecursive, collected, finished, Except.mapError] at accepted
    | ok value =>
      have same : value = catalog := by
        simpa [elaborateRecursive, collected, finished, Except.mapError] using accepted
      subst value
      exact ⟨pair.1, finishRecursive_source _ _ _ _ finished⟩
/-- A failed recursive elaboration cannot overwrite the previous publication. -/
def publishRecursive {FailureType : Type} (old : Catalog α) (candidate : Except FailureType (Catalog α)) : Catalog α :=
  match candidate with | .error _ => old | .ok next => next
/-- Both machine diagnostics and source refusals retain the same old catalog. -/
theorem publishRecursive_refused {FailureType : Type} (old : Catalog α) (failure : FailureType) :
    publishRecursive old (.error failure) = old := rfl
end LeanPoo.Functional.DeclarativeMetadata
