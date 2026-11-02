import LeanPoo.Functional.ClosureConstruction
import LeanPoo.Functional.CyclicAccess

/-! Dependency-equal syntax changes may change semantics. Reuse only the index;
recompute least closure and publish the completed admitted service family. -/
namespace LeanPoo.Examples.ReshapedAccess
open Functional PositiveEquations IncrementalClosure

def before : Equations 3 := fun index => match index.val with
  | 0 => .literal true
  | 1 => .both (.read 0) (.read 2)
  | _ => .read 1

def after : Equations 3 := fun index => match index.val with
  | 0 => .literal true
  | 1 => .either (.read 0) (.both (.literal false) (.read 2))
  | _ => .read 1

theorem same_reads (index : Fin 3) : collectDeps (after index) [] = collectDeps (before index) [] := by
  unfold after before
  split <;> rfl

/-- The shape-change fallback builds two temporary occurrence lists. This
additional allocation is separate from fused copying and retained index storage. -/
theorem reshape_read_packets (before after : Expr n)
    (same : collectDeps after [] = collectDeps before []) :
    (collectDeps before []).length + (collectDeps after []).length =
      2*(dependencies before).length := by
  rw [same]
  simp only [collectDeps_correct,List.append_nil]
  omega

#eval show IO Unit from do
  let plan := ClosureConstruction.compile before
  let revised := ClosureConstruction.reshape plan after (by intro index; rw [ClosureConstruction.compile_source]; exact same_reads index)
  let old := (ClosureLifecycle.prepare .cold plan).solve
  let next := (ClosureLifecycle.prepare .cold revised).solve
  unless !old.store[1] && next.store[1] && next.store[2] && revised.watches == plan.watches do
    throw (IO.userError "reshape with changed semantics")
  IO.println "RESHAPED-ACCESS-OK same-reads changed-semantics fresh-least-closure retained-index"
#print axioms reshape_read_packets
#print axioms ClosureConstruction.reshape_index
#print axioms ClosureConstruction.reshape_canonical
#print axioms CarrierMigration.publish_refused
#print axioms CyclicPublication.Version.least
#print axioms CyclicPublication.publishRetained_index
#print axioms CyclicPublication.publishRetained_refused
end LeanPoo.Examples.ReshapedAccess
