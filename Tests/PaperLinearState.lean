import LeanPoo.Prototype.LinearState
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperLinearState
private def run : IO Unit := do
  for seed in List.range 64 do
    let base := seed*3
    let initial ← LinearState.create base
    let snapshot ← IO.ofExcept (← initial.read)
    let alias := initial
    let next ← IO.ofExcept (← initial.step (fun value => .ok (value+1)))
    unless (← alias.read).toOption == none && !(← alias.step (fun value => .ok value)).isOk &&
        (← next.read).toOption == some (base+1) && snapshot == base do
      throw (IO.userError "old reference not consumed or snapshot changed")
    let refused ← next.step (fun _ => .error "refused")
    unless !refused.isOk && (← next.read).toOption == some (base+1) do
      throw (IO.userError "rejected transition consumed state")
    let updates : List (Nat → Except String Nat) := [fun x => .ok (x+2),fun x => .ok (x*3),fun x => .ok (x-1)]
    let threaded ← IO.ofExcept (← LinearState.run updates base)
    unless (← threaded.read).toOption == (LinearState.runPure updates base).toOption &&
        (← threaded.read).toOption == some ((base+2)*3-1) do
      throw (IO.userError "mutable threading differs from pure scalar oracle")
  let mut races := 0
  for _ in List.range 32 do
    let state ← LinearState.create (0 : Nat)
    let one ← IO.asTask (state.step (fun x => .ok (x+1))) .dedicated
    let two ← IO.asTask (state.step (fun x => .ok (x+2))) .dedicated
    let a ← IO.ofExcept one.get
    let b ← IO.ofExcept two.get
    unless ([a.isOk,b.isOk].filter id).length == 1 do throw (IO.userError "competing consumers both won or both lost")
    let winner ← IO.ofExcept (if a.isOk then a else b)
    let result ← IO.ofExcept (← winner.read)
    unless result == 1 || result == 2 do throw (IO.userError "winner value")
    unless !(← state.read).isOk do throw (IO.userError "raced reference remains live")
    races := races+1
  IO.println s!"POOF-LINEAR-STATE-OK scalarContexts=64 competingConsumers={races} snapshot=true aliasRefusal=true rejectPreserves=true"
#eval run
#print axioms LinearState.compose_assoc
end LeanPoo.Tests.PaperLinearState
