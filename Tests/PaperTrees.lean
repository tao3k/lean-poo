import LeanPoo.Prototype.AVL
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperTrees

private def height : Tree K V → Nat
  | .empty => 0
  | .node l _ _ _ r => 1 + max (height l) (height r)

-- Independent structural validator; never calls cachedHeight or avlNode.
private def validAVL : Tree Int Int → Option Int → Option Int → Bool
  | .empty, _, _ => true
  | .node l k _ cached r, lower, upper =>
    lower.all (· < k) && upper.all (k < ·) &&
    (cached == some (height (.node l k 0 cached r))) &&
    (height l ≤ height r+1) && (height r ≤ height l+1) &&
    validAVL l lower (some k) && validAVL r (some k) upper

private def insertEverywhere (x : Int) : List Int → List (List Int)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: ((insertEverywhere x ys).map (y :: ·))
private def permutations : List Int → List (List Int)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertEverywhere x)

private unsafe def sourceCases : IO Unit := do
  let numbers := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.number)
  let strings := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.string)
  let symbols := OrderOps.instantiate (OrderOps.symbol strings)
  -- All two original Order @Checks outcomes.
  unless numbers.less 23 42 && (numbers.compare 8 4).toOption == some .gt &&
      strings.less "Hello" "World" && (strings.compare "Foo" "FOO").toOption == some .gt &&
      (strings.compare "42" "42").toOption == some .eq do throw (IO.userError "paper:715")
  let s := Symbol.mk
  unless symbols.less (s "aardvark") (s "aaron") && symbols.equal (s "zzz") (s "zzz") &&
      symbols.greater (s "aa") (s "a") && (symbols.compare (s "alice") (s "bob")).toOption == some .lt &&
      (symbols.compare (s "b") (s "c")).toOption == some .lt && (symbols.compare (s "c") (s "a")).toOption == some .gt do
    throw (IO.userError "paper:731")
  let bst : Dictionary Symbol String (List String) := Dictionary.instantiate symbols Dictionary.binaryTree
  let avl : Dictionary Symbol String (List String) := Dictionary.instantiate symbols
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let entries := [(s "a","I"),(s "b","II"),(s "c","III"),(s "d","IV"),(s "e","V")]
  let plain ← IO.ofExcept (bst.fromList entries)
  let balanced ← IO.ofExcept (avl.fromList entries)
  let leaf := fun k v h => Tree.node Tree.empty (s k) v h Tree.empty
  let expectedPlain := Tree.node .empty (s "a") "I" none
    (.node .empty (s "b") "II" none (.node .empty (s "c") "III" none
      (.node .empty (s "d") "IV" none (leaf "e" "V" none))))
  let expectedAVL := Tree.node (leaf "a" "I" (some 1)) (s "b") "II" (some 3)
    (.node (leaf "c" "III" (some 1)) (s "d") "IV" (some 2) (leaf "e" "V" (some 1)))
  unless plain == expectedPlain && height plain == 5 do throw (IO.userError "paper:792")
  unless balanced == expectedAVL && height balanced == 3 do throw (IO.userError "paper:839")
  for (dictionary,label) in [(bst,"paper:797"),(avl,"paper:842")] do
    let tree ← IO.ofExcept (dictionary.fromList entries)
    let values ← IO.ofExcept ((["a","b","c","d","e","z"].map s).mapM (dictionary.ref tree))
    unless values == [some "I",some "II",some "III",some "IV",some "V",none] do
      throw (IO.userError label)
    unless dictionary.afoldr (fun k _ acc => k.name :: acc) [] tree == ["e","d","c","b","a"] do
      throw (IO.userError "paper afoldr order")
    let changed ← IO.ofExcept (dictionary.acons (s "c") "replacement" tree)
    unless (← IO.ofExcept (dictionary.ref changed (s "c"))) == some "replacement" &&
        (← IO.ofExcept (dictionary.ref tree (s "c"))) == some "III" && changed.size == 5 do
      throw (IO.userError "overwrite or retained snapshot")
  -- Final-self rebinding, incomparable order, and incompatible AVL data controls.
  let reversed := OrderOps.instantiate (DelayedProto.compose
    (OrderOps.predicates (fun x y : Int => decide (x > y)) (· == ·) (fun x y => decide (x < y)))
    (DelayedProto.compose OrderOps.compareMixin OrderOps.number))
  unless (reversed.compare 1 2).toOption == some .gt do throw (IO.userError "compare mixin lost final self")
  let incomparable : OrderOps Int := OrderOps.instantiate OrderOps.compareMixin
  unless (match incomparable.compare 1 2 with | .error "incomparable" => true | _ => false) do throw (IO.userError "missing comparison refusal")
  unless !(Dictionary.avlNode plain (s "f") "VI" .empty).isOk do
    throw (IO.userError "unannotated AVL children admitted")
  IO.println "POOF-TREES-SOURCE-OK checks=6 bstHeight=5 avlHeight=3 lookupCases=12 finalSelf=true"

private unsafe def exercise : IO Unit := do
  let order := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.number)
  let dictionary : Dictionary Int Int (List Int) := Dictionary.instantiate order
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let mut updates := 0
  let perms := permutations [0,1,2,3,4,5]
  unless perms.length == 720 do throw (IO.userError "permutation coverage drift")
  let mut traces := perms
  for seed in List.range 64 do
    let mut state := seed+1
    let mut trace := []
    for _ in List.range 32 do
      state := (state*1664525+1013904223) % 4294967296
      trace := Int.ofNat ((state / 65536) % 16) :: trace
    traces := trace :: traces
  for trace in traces do
    let mut tree : Tree Int Int := .empty
    let mut model : List (Int × Int) := []
    for key in trace do
      let value := Int.ofNat updates
      tree ← IO.ofExcept (dictionary.acons key value tree)
      model := (key,value) :: model.filter (fun entry => entry.1 != key)
      unless validAVL tree none none && tree.size == model.length do
        throw (IO.userError "structural AVL ordering/balance/height/size")
      for query in List.range 18 do
        let wanted := (model.find? (fun entry => entry.1 == Int.ofNat query)).map Prod.snd
        unless (← IO.ofExcept (dictionary.ref tree (Int.ofNat query))) == wanted do
          throw (IO.userError "AVL lookup differs from retained association-list oracle")
      updates := updates+1
  -- Each 3-key order triggers one of LL, LR, RL and RR.
  for keys in [[3,2,1],[3,1,2],[1,3,2],[1,2,3]] do
    let tree ← IO.ofExcept (dictionary.fromList (keys.map fun key => (key,key)))
    let expected : Tree Int Int := .node (.node .empty 1 1 (some 1) .empty)
      2 2 (some 2) (.node .empty 3 3 (some 1) .empty)
    unless tree == expected do throw (IO.userError "rotation shape drift")
  unless updates == 6368 do throw (IO.userError "update coverage drift")
  IO.println s!"POOF-AVL-ORACLE-OK permutations=720 seededTraces=64 updates={updates} rotations=4"

#eval sourceCases
#eval exercise
#print axioms Dictionary.avlRebalance_inherits
#print axioms Dictionary.avlRebalance_node
end LeanPoo.Tests.PaperTrees
