import LeanPoo.Functional.Access

/-! Give a consumer only its declared capability dependencies. Projection uses
retained functions; it does not compile a graph, query a provider, or run them. -/
namespace LeanPoo.Functional.Requirements

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Narrow a prepared family to a consumer's keys, in the consumer's order.
Each access scans the source list. Project once before repeated application. -/
def project [DecidableEq Key] {source : List Key}
    (retained : Factories Context Value source) :
    (keys : List Key) → (∀ key ∈ keys, key ∈ source) → Factories Context Value keys
  | [], _ => PUnit.unit
  | key :: rest, included =>
    (factoryAt retained key (included key (by simp)),
      project retained rest (fun key member => included key (by simp [member])))

/-- Projection retains the exact selected functions, including duplicates. -/
theorem project_selected [DecidableEq Key] (provider : Provider Context Key Value)
    (retained : Factories Context Value source) (selected : Selected provider source retained)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) :
    Selected provider keys (project retained keys included) := by
  induction keys with
  | nil => trivial
  | cons key rest ih =>
    exact ⟨factoryAt_selected provider source retained selected key _, ih _⟩

/-- Narrowing an available family agrees with independent local preparation. -/
theorem project_ready [DecidableEq Key] (provider : Provider Context Key Value)
    (retained : Factories Context Value source)
    (ready : prepare provider source = .ok retained)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) :
    prepare provider keys = .ok (project retained keys included) :=
  (prepare_ok_iff _ _ _).mpr (project_selected provider retained
    ((prepare_ok_iff _ _ _).mp ready) keys included)

/-- Unrequested provider changes and successful source-list changes cannot
alter this consumer's view. Agreement is needed only on its declared keys. -/
theorem project_stable [DecidableEq Key] (provider other : Provider Context Key Value)
    (left : Factories Context Value leftKeys) (right : Factories Context Value rightKeys)
    (leftReady : prepare provider leftKeys = .ok left)
    (rightReady : prepare other rightKeys = .ok right)
    (keys : List Key) (a : ∀ key ∈ keys, key ∈ leftKeys)
    (b : ∀ key ∈ keys, key ∈ rightKeys)
    (same : ∀ key ∈ keys, other key = provider key) :
    project left keys a = project right keys b := by
  have first := project_ready provider left leftReady keys a
  have second := project_ready other right rightReady keys b
  rw [prepare_congr provider other keys same] at second
  exact Except.ok.inj (first.symm.trans second)

/-- Every consumer of the narrow interface has the same result under these
changes. Result may itself be a function over all contexts or a proof family. -/
theorem consumer_stable [DecidableEq Key] (provider other : Provider Context Key Value)
    (left : Factories Context Value leftKeys) (right : Factories Context Value rightKeys)
    (leftReady : prepare provider leftKeys = .ok left)
    (rightReady : prepare other rightKeys = .ok right)
    (keys : List Key) (a : ∀ key ∈ keys, key ∈ leftKeys)
    (b : ∀ key ∈ keys, key ∈ rightKeys)
    (same : ∀ key ∈ keys, other key = provider key)
    (consume : Factories Context Value keys → Result) :
    consume (project left keys a) = consume (project right keys b) :=
  congrArg consume (project_stable provider other left right leftReady rightReady keys a b same)

end LeanPoo.Functional.Requirements
