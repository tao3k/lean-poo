import LeanPoo.Functional.Requirements

/-! Adapt a capability family to an outer context without changing selection,
missing-key order, or the exact projected context of its dependent results. -/
namespace LeanPoo.Functional

universe u v w x
variable {Context : Type u} {Outer : Type x} {Key : Type v}
variable {Value : Context → Key → Type w}

/-- Adapt each available factory; no context or factory is evaluated here. -/
def reindexProvider (project : Outer → Context) (provider : Provider Context Key Value) :
    Provider Outer Key (fun outer key => Value (project outer) key) :=
  fun key => (provider key).map (Factory.reindex project)

/-- Context projection commutes with first-provider precedence selection. -/
theorem select_reindex (project : Outer → Context) (names : List String)
    (providers : String → Provider Context Key Value) (key : Key) :
    select names (fun name => reindexProvider project (providers name)) key =
      (select names providers key).map (Factory.reindex project) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    cases found : providers name key <;> simp [select, reindexProvider, found, ih]

/-- Reuse the same verified order; no graph compilation is added. -/
theorem assemble_reindex (project : Outer → Context) (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) :
    assemble order (fun name => reindexProvider project (providers name)) =
      reindexProvider project (assemble order providers) := by
  funext key
  exact select_reindex project order.output providers key

namespace Requirements

/-- Adapt an already prepared tuple once. Result types retain the projection. -/
def reindex (project : Outer → Context) : {keys : List Key} → Factories Context Value keys →
    Factories Outer (fun outer key => Value (project outer) key) keys
  | [], _ => PUnit.unit
  | _ :: _, (factory, tail) => (Factory.reindex project factory, reindex project tail)

/-- Reindex before or after preparation with exactly the same success/first
missing-key result. This maps functions; neither path invokes the factories. -/
theorem prepare_reindex (project : Outer → Context) (provider : Provider Context Key Value)
    (keys : List Key) :
    prepare (reindexProvider project provider) keys =
      (prepare provider keys).map (reindex project) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    cases found : provider key with
    | none => simp [prepare, reindexProvider, found, Except.map]
    | some factory =>
      rw [prepare, reindexProvider, found]
      simp only [Option.map_some]
      rw [ih]
      cases remaining : prepare provider rest <;>
        simp [prepare, found, remaining, Except.map, reindex]

/-- The generic result tuple types agree after substituting the projection. -/
theorem results_reindex_type (project : Outer → Context) (keys : List Key) (outer : Outer) :
    Results (fun outer key => Value (project outer) key) outer keys =
      Results Value (project outer) keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih => exact congrArg (fun tail => Value (project outer) key × tail) ih

/-- Identify adapted tuple results with their original projected-context type.
The equality cast adds no result traversal or factory invocation. -/
def projectedResults (project : Outer → Context) (keys : List Key) (outer : Outer)
    (results : Results (fun outer key => Value (project outer) key) outer keys) :
    Results Value (project outer) keys := cast (results_reindex_type project keys outer) results

private theorem cast_pair {Head Tail Other : Type w} (same : Tail = Other)
    (head : Head) (tail : Tail) :
    cast (congrArg (fun rest => Head × rest) same) (head, tail) = (head, cast same tail) := by
  cases same; rfl

/-- Applying the adapted tuple returns the original results at exactly the
projected context, including proof-bearing dependent result families. -/
theorem build_reindex (project : Outer → Context) (keys : List Key)
    (retained : Factories Context Value keys) (outer : Outer) :
    projectedResults project keys outer (build (reindex project retained) outer) =
      build retained (project outer) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    rcases retained with ⟨factory, tail⟩
    change cast (congrArg (fun rest => Value (project outer) key × rest)
        (results_reindex_type project rest outer))
      (factory (project outer), build (reindex project tail) outer) = _
    rw [cast_pair (results_reindex_type (Value := Value) project rest outer)]
    exact Prod.ext rfl (ih tail)

end Requirements
end LeanPoo.Functional
