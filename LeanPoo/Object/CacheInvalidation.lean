import LeanPoo.Proof.Invalidation

/-! Mutable native sources clear derived state together. The graph models all
registered source edges (parents, hooks and descriptors). Correct registration,
sequential evaluation and graph finiteness are explicit native obligations. -/
namespace LeanPoo.Object
/-- One retained derived cache cell, tagged by the source's logical revision. -/
structure RevisionCache (Value : Type) where
  revision : Nat
  derived : Option Value
/-- Clear every reached owner; retain unaffected owners exactly. -/
def invalidateCaches (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) : String → RevisionCache Value :=
  fun name => if name ∈ Proof.invalidatedNodes graph changed then
    ⟨(cache name).revision + 1, none⟩ else cache name
/-- A finite registered path always clears its descendant, including shared joins. -/
theorem invalidateCaches_descendant (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (origin name : String) (steps : Nat)
    (member : origin ∈ changed) (path : Proof.Descendant graph origin steps name)
    (bounded : steps ≤ graph.nodes.length) :
    (invalidateCaches graph changed cache name).derived = none := by
  simp [invalidateCaches, Proof.mem_invalidated_of_descendant graph changed origin name steps member path bounded]
/-- A source edit advances a shared descendant exactly once, regardless of path count. -/
theorem invalidateCaches_once (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (name : String)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    (invalidateCaches graph changed cache name).revision = (cache name).revision + 1 := by
  simp [invalidateCaches, affected]
/-- An owner outside the registered reverse closure is unchanged. -/
theorem invalidateCaches_frame (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (name : String)
    (untouched : name ∉ Proof.invalidatedNodes graph changed) :
    invalidateCaches graph changed cache name = cache name := by simp [invalidateCaches, untouched]
/-- Native preflight rejects sealed sources or edits during any affected computation. -/
def guardedEdit (sealed active : Bool) (old : State) (edit : State → State) : Except String State :=
  if sealed then .error "sealed prototype" else
  if active then .error "object mutation during computation" else .ok (edit old)
/-- A refused edit publishes the caller's original source exactly. -/
def publishEdit (old : State) (result : Except String State) : State :=
  match result with | .error _ => old | .ok next => next
/-- Source refusal does not invoke an edit or advance the published revision. -/
theorem publishEdit_sealed (old : State) (edit : State → State) (active : Bool) :
    publishEdit old (guardedEdit true active old edit) = old := rfl

/-- Root preflight has already run. Its successful snapshot records whether a
weak dependency table exists and the current children, including newly registered
ones. The existing checked traversal returns descendant-first owners without root.
This models a finite faithful graph, not weak-table collection or callback rollback. -/
def invalidationAfterCheck (root : Node) (checked : Except Cause (Bool × List Node))
    (walk : List Node → Except Cause (List Node)) : Except Cause (List Node) := do
  let (retained, children) ← checked
  if retained then
    let owners ← walk children
    pure (owners ++ [root])
  else pure [root]

/-- Reference traversal preparation always handles the admitted root's children. -/
def generalInvalidationOrder (root : Node) (checked : Except Cause (Bool × List Node))
    (walk : List Node → Except Cause (List Node)) : Except Cause (List Node) := do
  let (_, children) ← checked
  let owners ← walk children
  pure (owners ++ [root])

/-- A pristine post-check leaf never calls the graph walker. -/
theorem invalidationAfterCheck_leaf (root : Node)
    (walk : List Node → Except Cause (List Node)) :
    invalidationAfterCheck root (.ok (false, [])) walk = .ok [root] := rfl

/-- Root refusal keeps its exact cause, including false-like host exceptions. -/
theorem invalidationAfterCheck_refused (root : Node) (cause : Cause)
    (walk : List Node → Except Cause (List Node)) :
    invalidationAfterCheck root (.error cause) walk = .error cause := rfl

/-- Registered dependencies, even an empty retained table, keep the old traversal.
The faithful-absence premise is required only for the pristine branch. -/
theorem invalidationAfterCheck_eq_general (root : Node) (retained : Bool)
    (children : List Node) (walk : List Node → Except Cause (List Node))
    (absent : retained = false → children = []) (empty : walk [] = .ok []) :
    invalidationAfterCheck root (.ok (retained, children)) walk =
      generalInvalidationOrder root (.ok (retained, children)) walk := by
  cases retained with
  | false => have h := absent rfl; subst children
             change (.ok [root] : Except Cause (List Node)) =
               (walk []).map (fun owners => owners ++ [root])
             rw [empty]; rfl
  | true => rfl

/-- A child added during root preflight is checked; refusal cannot become a leaf hit. -/
theorem invalidationAfterCheck_child_refused (root : Node) (children : List Node)
    (cause : Cause) (walk : List Node → Except Cause (List Node))
    (refused : walk children = .error cause) :
    invalidationAfterCheck root (.ok (true, children)) walk = .error cause := by
  change (walk children).map (fun owners => owners ++ [root]) = .error cause
  rw [refused]; rfl

/-- Revision advancement precedes clear. Clear return values are discarded, but
clear failures do not roll back the revision, matching the existing callback API. -/
def finishInvalidation (old : RevisionCache Value) (cleared : Except Cause Result) :
    RevisionCache Value × Except Cause Unit :=
  (⟨old.revision + 1, none⟩, cleared.map (fun _ => ()))

/-- Function/false/multiple-value payloads do not escape the unit-return boundary. -/
theorem finishInvalidation_ok (old : RevisionCache Value) (result : Result) :
    finishInvalidation old (Except.ok result : Except Cause Result) =
      (⟨old.revision + 1, none⟩, .ok ()) := rfl

/-- A thrown clear failure still leaves its already advanced source generation. -/
theorem finishInvalidation_error (old : RevisionCache Value) (cause : Cause) :
    finishInvalidation old (Except.error cause : Except Cause Unit) =
      (⟨old.revision + 1, none⟩, .error cause) := rfl

/-- Logical temporary counts: one traversal table and two list/pair cells per
pending owner on the retained path; no physical allocation or GC theorem. -/
def invalidationScratch (retained : Bool) (owners : Nat) : Nat × Nat :=
  if retained then (1, 2 * owners) else (0, 0)

/-- Every pristine leaf avoids the reference path's one table and two cells. -/
theorem invalidationScratch_leaf : invalidationScratch false 1 = (0, 0) ∧
    invalidationScratch true 1 = (1, 2) := ⟨rfl, rfl⟩

/-- Existing reverse-closure semantics specialize to a singleton without changing
unrelated owners, revisions or cached Function payloads. Closure fidelity remains
an explicit hypothesis; this does not decide whether a weak key was collected. -/
theorem invalidateCaches_leaf (graph : C4.Graph) (root : String)
    (cache : String → RevisionCache Value)
    (closure : Proof.invalidatedNodes graph [root] = [root]) :
    invalidateCaches graph [root] cache = fun name =>
      if name = root then ⟨(cache name).revision + 1, none⟩ else cache name := by
  funext name
  simp [invalidateCaches, closure]

end LeanPoo.Object
