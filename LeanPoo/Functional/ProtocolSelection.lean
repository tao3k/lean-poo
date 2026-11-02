import Init.Data.List.Find
import Init.Data.List.Impl

/-! Pure first-protocol lookup for checked precedence orders.
This advances generalized MOP future work; host traversal and mutation need
separate executable controls. No new protocol namespace is introduced. -/
namespace LeanPoo.Functional.InheritedMOP

/-- Select one complete protocol from an already checked precedence order.
`none` models Scheme false; a selected protocol may itself have no named hook.
This pure lookup does not certify C3, mutation, effects or runtime traversal. -/
def selectProtocol (lookup : Name → Option Protocol) (order : List Name) : Option Protocol :=
  order.findSome? lookup

/-- A selected protocol shadows every later branch, even if it lacks a hook. -/
theorem selectProtocol_first (lookup : Name → Option Protocol) (name : Name)
    (protocol : Protocol) (tail : List Name) (selected : lookup name = some protocol) :
    selectProtocol lookup (name :: tail) = some protocol := by
  simp [selectProtocol, List.findSome?, selected]

/-- An absent direct protocol delegates to the current inherited suffix. -/
theorem selectProtocol_absent (lookup : Name → Option Protocol) (name : Name)
    (tail : List Name) (absent : lookup name = none) :
    selectProtocol lookup (name :: tail) = selectProtocol lookup tail := by
  simp [selectProtocol, List.findSome?, absent]

/-- No protocol is selected exactly when every ordered source lacks one. -/
theorem selectProtocol_none (lookup : Name → Option Protocol) (order : List Name) :
    selectProtocol lookup order = none ↔ ∀ name ∈ order, lookup name = none := by
  exact List.findSome?_eq_none_iff

/-- Revisions confined to the suffix cannot change an already selected prefix.
Runtime callback non-evaluation is checked separately in Gerbil. -/
theorem selectProtocol_prefix (lookup : Name → Option Protocol) (front tail : List Name)
    (protocol : Protocol) (selected : selectProtocol lookup front = some protocol) :
    selectProtocol lookup (front ++ tail) = some protocol := by
  simp only [selectProtocol, List.findSome?_append] at *
  simp [selected]
end LeanPoo.Functional.InheritedMOP
