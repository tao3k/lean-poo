import LeanPoo.Object.Callable
import LeanPoo.Prototype.SharedThunkHeap

/-! Checked native shared closures for actual C3 field and parameterized method
plans. Receipts retain the exact immutable program; source C3 derivations transfer
through the existing plan laws. These closures share construction, not a request
memo table. The safe Cached runtime remains available for request memoization. -/
namespace LeanPoo.Object

open Prototype
open Prototype.Recursive
open Prototype.Recursive.Shared

namespace Recursive

unsafe def Plan.sharedRuntime (plan : Plan) : Runtime (MutableRecord.generator plan.storage) :=
  Runtime.new _

unsafe def Plan.boundedSharedRuntime (plan : Plan) (depth : Nat) :
    Runtime (MutableRecord.generator plan.storage) := Runtime.bounded _ depth

theorem Plan.shared_observed (plan : Plan)
    (runtime : Runtime (MutableRecord.generator plan.storage)) (key : String)
    (receipt : Cached.Receipt (MutableRecord.generator plan.storage)
      (MutableRecord.generator plan.storage key)) (accepted : runtime.read key = .ok receipt) :
    ∃ depth, plan.read depth key = (runtime.executor key).result :=
  runtime.read_observed key receipt accepted

theorem Plan.shared_derivation (plan : Plan)
    (runtime : Runtime (MutableRecord.generator plan.storage)) (key : String)
    (receipt : Cached.Receipt (MutableRecord.generator plan.storage)
      (MutableRecord.generator plan.storage key)) (accepted : runtime.read key = .ok receipt)
    (order : List String) (derived : Prototype.C3.GraphDerivation plan.schema.graph plan.root order) :
    ∃ depth, MutableRecord.readPure
      ((plan.schema.specification order).transition plan.schema.base).1 depth key =
        (runtime.executor key).result := by
  obtain ⟨depth, observed⟩ := plan.shared_observed runtime key receipt accepted
  exact ⟨depth, (plan.read_derivation order derived depth key).symm.trans observed⟩

end Recursive

namespace Callable

unsafe def Plan.sharedRuntime (plan : Plan Argument) : Runtime plan.program := Runtime.new _

unsafe def Plan.boundedSharedRuntime (plan : Plan Argument) (depth : Nat) : Runtime plan.program :=
  Runtime.bounded _ depth

theorem Plan.shared_observed (plan : Plan Argument) (runtime : Runtime plan.program)
    (input : CallableRecord.Request Argument) (receipt : Cached.Receipt plan.program (plan.program input))
    (accepted : runtime.read input = .ok receipt) :
    ∃ depth, plan.call depth input = (runtime.executor input).result :=
  runtime.read_observed input receipt accepted

theorem Plan.shared_derivation (plan : Plan Argument) (runtime : Runtime plan.program)
    (input : CallableRecord.Request Argument) (receipt : Cached.Receipt plan.program (plan.program input))
    (accepted : runtime.read input = .ok receipt) (order : List String)
    (derived : Prototype.C3.GraphDerivation plan.schema.graph plan.root order) :
    ∃ depth, CallableRecord.readPure
      (plan.schema.specification order request plan.schema.base) depth input =
        (runtime.executor input).result := by
  obtain ⟨depth, observed⟩ := plan.shared_observed runtime input receipt accepted
  exact ⟨depth, (plan.call_derivation order derived depth input).symm.trans observed⟩

end Callable
end LeanPoo.Object
