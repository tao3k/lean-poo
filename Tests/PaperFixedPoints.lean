import LeanPoo.Prototype.CheckedFunction
import LeanPoo.Prototype.Delayed
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperFixedPoints
private unsafe def run : IO Unit := do
  let bottom : CheckedFunction Nat Nat := CheckedFunction.instance []
  unless (bottom 3).toOption == none do throw (IO.userError "source bottom default")
  let terminal : CheckedFunction Nat Nat := FixedFunction.ofFun fun x => .ok (x+7)
  let closed := CheckedFunction.instance [constant terminal]
  unless (closed 3).toOption == some 10 do throw (IO.userError "source constant tail did not bypass bottom")
  let recursive : Proto (CheckedFunction Nat Nat) (CheckedFunction Nat Nat) (CheckedFunction Nat Nat) :=
    fun self _ => FixedFunction.ofFun fun n =>
      if n == 0 then .ok 0 else do return (← self (n-1))+n
  let shared := CheckedFunction.instance [recursive]
  let rebuilt := rebuildingFix recursive CheckedFunction.bottom
  for n in List.range 65 do
    unless (shared n).toOption == some (n*(n+1)/2) && (rebuilt n).toOption == (shared n).toOption do
      throw (IO.userError "fixed point variants differ from triangular scalar oracle")
  let sharedCount ← IO.mkRef (0 : Nat)
  let rebuildCount ← IO.mkRef (0 : Nat)
  let counted (counter : IO.Ref Nat) : Proto (FixedFunction Nat Nat) Unit (FixedFunction Nat Nat) :=
    fun _ _ => unsafeBaseIO do
      counter.modify (·+1)
      return FixedFunction.ofFun fun n => n+1
  let sharedCalls := instantiate (counted sharedCount) ()
  let rebuildCalls := rebuildingFix (counted rebuildCount) ()
  for n in List.range 32 do
    unless sharedCalls n == n+1 && rebuildCalls n == n+1 do throw (IO.userError "counted function value")
  unless (← sharedCount.get) == 1 && (← rebuildCount.get) == 32 do
    throw (IO.userError "fixed point sharing distinction")
  let delayedCount ← IO.mkRef (0 : Nat)
  let delayed : DelayedProto Nat Nat Nat := fun _ inherited => unsafeBaseIO do
    delayedCount.modify (·+1)
    return inherited.get+1
  let value := DelayedProto.instantiate delayed (Thunk.pure 30)
  for _ in List.range 32 do
    unless value.get == 31 do throw (IO.userError "delayed nonfunction value")
  unless (← delayedCount.get) == 1 do throw (IO.userError "delayed knot rebuilt")
  IO.println "POOF-FIXED-POINTS-OK triangularInputs=65 sharedBuilds=1 rebuildingBuilds=32 delayedBuilds=1 bottom=true constantTail=true"
#eval run
#print axioms CheckedFunction.bottom_apply
end LeanPoo.Tests.PaperFixedPoints
