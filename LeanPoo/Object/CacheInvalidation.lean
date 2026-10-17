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
end LeanPoo.Object
