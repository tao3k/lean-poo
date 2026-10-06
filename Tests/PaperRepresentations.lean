import LeanPoo.Prototype.AVL
import LeanPoo.Prototype.KeyedPrototype
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperRepresentations
private unsafe def run : IO Unit := do
  let order := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.number)
  let pairs : Dictionary Int Int (List (Int × Int)) := Dictionary.instantiate order
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let merges : Dictionary Int Int (Except String (Tree Int Int)) := Dictionary.instantiate order
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let base ← IO.ofExcept (pairs.fromList [(1,10),(2,20),(3,30)])
  let overrideTree ← IO.ofExcept (pairs.fromList [(2,200),(4,400)])
  let result ← IO.ofExcept (merges.merge overrideTree base)
  unless pairs.toList result == [(4,400),(3,30),(2,200),(1,10)] &&
      pairs.toList base == [(3,30),(2,20),(1,10)] do throw (IO.userError "dictionary helpers or retained base")
  for count in List.range 33 do
    let left := (List.range count).map (fun key => (Int.ofNat key,Int.ofNat (key+100)))
    let right := (List.range (count+1)).map (fun key => (Int.ofNat key,Int.ofNat key))
    let l ← IO.ofExcept (pairs.fromList left)
    let r ← IO.ofExcept (pairs.fromList right)
    let merged ← IO.ofExcept (merges.merge l r)
    for key in List.range (count+2) do
      let query := Int.ofNat key
      let want := ((left.find? (·.1 == query)).orElse (fun _ => right.find? (·.1 == query))).map Prod.snd
      unless (← IO.ofExcept (pairs.ref merged query)) == want do throw (IO.userError "dictionary merge scalar oracle")
  let x1 : KeyedPrototype.Definition String (fun _ => Int) := KeyedPrototype.slot "x" 1
  let y2 : KeyedPrototype.Definition String (fun _ => Int) := KeyedPrototype.slot "y" 2
  let x3 : KeyedPrototype.Definition String (fun _ => Int) := KeyedPrototype.slot "x" 3
  let definitions := KeyedPrototype.compose x3 (KeyedPrototype.compose y2 x1)
  let closed := KeyedPrototype.instantiate definitions
  unless closed.lookup (.inr ()) == some ["x","y","x"] &&
      closed.lookup (.inl "x") == some 3 && closed.lookup (.inl "y") == some 2 &&
      closed.lookup (.inl "missing") == none do throw (IO.userError "key-list representation")
  let overridden := DelayedProto.compose
    (Object.recordSlotGen (.inr ()) (fun _ _ => some ["public"])) definitions.layer
  let change : KeyedPrototype.Definition String (fun _ => Int) :=
    { definitions with layer := overridden }
  unless (KeyedPrototype.instantiate change).lookup (.inr ()) == some ["x","y","x"] &&
      (KeyedPrototype.instantiate change Record.empty true).lookup (.inr ()) == some ["public"] do
    throw (IO.userError "key-slot precedence policy")
  IO.println "POOF-REPRESENTATIONS-OK mergeContexts=33 mergeReads=594 duplicateKeys=true keysOverride=true"
#eval run
end LeanPoo.Tests.PaperRepresentations
