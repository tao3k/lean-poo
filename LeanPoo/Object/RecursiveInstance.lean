import LeanPoo.Object.Recursive
import LeanPoo.Prototype.RecursiveCacheSemantics

/-! Shared lazy instances for certified recursive objects. The cache is indexed
by the plan's exact immutable generator and carries evaluation proofs. -/
namespace LeanPoo.Object.Recursive

open Prototype
open Prototype.Recursive
open Prototype.MutableRecord

structure Instance (plan : Plan) where private mk ::
  private cache : Std.Mutex (Cached.Cache (generator plan.storage))

/-- A fresh lazy identity; no slot is evaluated during construction. -/
def Plan.instantiate (plan : Plan) : IO (Instance plan) := do
  return ⟨← Std.Mutex.new {}⟩

def Instance.readCertified (instanceValue : Instance plan) (budget : Nat) (key : String) :
    IO (Except (Cached.Failure (generator plan.storage) key) (Cached.Receipt (generator plan.storage)
      (generator plan.storage key))) := instanceValue.cache.atomically do
  match Cached.runCertified (generator plan.storage) key budget (← get) with
  | .error diagnostic => return .error diagnostic
  | .ok (receipt, next) =>
    set next
    return .ok receipt

def Instance.read (instanceValue : Instance plan) (budget : Nat) (key : String) :
    IO (Except (Cached.Diagnostic String) (Cached.Receipt (generator plan.storage)
      (generator plan.storage key))) := do
  return (← instanceValue.readCertified budget key).mapError Cached.Failure.diagnostic

def Instance.statistics (instanceValue : Instance plan) : IO Cached.Statistics :=
  instanceValue.cache.atomically do return (← get).statistics

def Instance.cachedKeys (instanceValue : Instance plan) : IO (List String) :=
  instanceValue.cache.atomically do return (← get).entries.map Cached.Entry.input

/-- A cached successful read agrees with every completed finite plan read. -/
theorem Instance.read_agrees {plan : Plan} {key : String} (receipt : Cached.Receipt (generator plan.storage)
    (generator plan.storage key)) (depth : Nat) (known : plan.read depth key ≠ .pending) :
    plan.read depth key = receipt.result.observation :=
  receipt.agrees depth known

end LeanPoo.Object.Recursive
