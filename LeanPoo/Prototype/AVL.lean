import LeanPoo.Prototype.BinaryTree

/-! POOF AVL extension: override node only; retain all dictionary algorithms. -/
namespace LeanPoo.Prototype
variable {Key Value Acc : Type}

private def avlMake (left : Tree Key Value) (key : Key) (value : Value)
    (right : Tree Key Value) : Except String (Tree Key Value) := do
  let lh ← left.cachedHeight
  let rh ← right.cachedHeight
  if lh > rh+1 || rh > lh+1 then throw "tree unbalanced"
  return .node left key value (some (1 + max lh rh)) right

/-- Rebuild a node, applying the source LL/LR/RL/RR cases and height guards. -/
def Dictionary.avlNode (left : Tree Key Value) (key : Key) (value : Value)
    (right : Tree Key Value) : Except String (Tree Key Value) := do
  let lh ← left.cachedHeight
  let rh ← right.cachedHeight
  let delta := (Int.ofNat rh) - (Int.ofNat lh)
  if -1 ≤ delta && delta ≤ 1 then return ← avlMake left key value right
  else if delta == -2 then
    match left with
    | .empty => throw "missing left rotation child"
    | .node ll lk lv _ lr =>
      let balance := Int.ofNat (← lr.cachedHeight) - Int.ofNat (← ll.cachedHeight)
      if balance == -1 || balance == 0 then
        return ← avlMake ll lk lv (← avlMake lr key value right)
      else if balance == 1 then
        match lr with
        | .empty => throw "missing left-right rotation child"
        | .node lrl lrk lrv _ lrr =>
          return ← avlMake (← avlMake ll lk lv lrl) lrk lrv (← avlMake lrr key value right)
      else throw "invalid left child balance"
  else if delta == 2 then
    match right with
    | .empty => throw "missing right rotation child"
    | .node rl rk rv _ rr =>
      let balance := Int.ofNat (← rr.cachedHeight) - Int.ofNat (← rl.cachedHeight)
      if balance == -1 then
        match rl with
        | .empty => throw "missing right-left rotation child"
        | .node rll rlk rlv _ rlr =>
          return ← avlMake (← avlMake left key value rll) rlk rlv (← avlMake rlr rk rv rr)
      else if balance == 0 || balance == 1 then
        return ← avlMake (← avlMake left key value rl) rk rv rr
      else throw "invalid right child balance"
  else throw "node imbalance exceeds one insertion"

/-- The only changed method is node; insert/ref/fold remain inherited. -/
def Dictionary.avlRebalance :
    DelayedProto (Dictionary Key Value Acc) (Dictionary Key Value Acc) (Dictionary Key Value Acc) :=
  fun _ inherited => { inherited.get with node := Dictionary.avlNode }

/-- AVL inherits the exact same insertion, lookup and fold method closures. -/
theorem Dictionary.avlRebalance_inherits (self inherited : Thunk (Dictionary Key Value Acc)) :
    (avlRebalance self inherited).acons = inherited.get.acons ∧
    (avlRebalance self inherited).ref = inherited.get.ref ∧
    (avlRebalance self inherited).afoldr = inherited.get.afoldr ∧
    (avlRebalance self inherited).singleton = inherited.get.singleton ∧
    (avlRebalance self inherited).keyOrder = inherited.get.keyOrder :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Dictionary.avlRebalance_node (self inherited : Thunk (Dictionary Key Value Acc)) :
    (avlRebalance self inherited).node = avlNode := rfl

end LeanPoo.Prototype
