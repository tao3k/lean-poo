import LeanPoo.Prototype.RecordRepresentations
import LeanPoo.Object.MultimethodSemantics

open LeanPoo.Prototype
namespace LeanPoo.Tests.ConstructionSemantics

-- Generic clients use the universal proofs, rather than finite-case automation.
example (tree : Tree Int Value) (key : Int) (value : Value) (valid : tree.ValidAVL) :
    ∃ output, tree.insert OrderOps.integer.compare Dictionary.avlNode key value = .ok output ∧
      output.ValidAVL ∧ tree.height ≤ output.height ∧ output.height ≤ tree.height+1 :=
  tree.avl_insert_complete OrderOps.integer OrderOps.integer_laws.total key value valid

example (entries : List (Int × Value)) :
    ∃ tree, (Dictionary.avl (Acc := Unit) OrderOps.integer).fromList entries = .ok tree ∧
      tree.ValidAVL ∧ tree.Sorted (· < ·) ∧
      ∀ query, (Dictionary.avl (Acc := Unit) OrderOps.integer).ref tree query =
        (entries.foldl Dictionary.updateView (fun _ => .ok none)) query :=
  Dictionary.avl_fromList OrderOps.integer (· < ·) OrderOps.integer_laws entries

example (key : Int) (body : SlotBody Int Value) :
    LayersRelated OrderOps.integer (· < ·)
      (DictionaryRecord.semanticSlot key body) (FunctionRecord.semanticSlot key body) :=
  semanticSlot_related OrderOps.integer (· < ·) OrderOps.integer_laws key body

private def sameOutcome [BEq α] : Except String α → Except String α → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private unsafe def run : IO Unit := do
  let sourceOrder := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.number)
  let source : Dictionary Int Int Unit := Dictionary.instantiate sourceOrder
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let certified : Dictionary Int Int Unit := Dictionary.avl OrderOps.integer
  let mut writes := 0
  for size in List.range 33 do
    let entries := (List.range size).map fun n => (Int.ofNat (n % 9), Int.ofNat (100+n))
    let original ← IO.ofExcept (source.fromList entries)
    let checked ← IO.ofExcept (certified.fromList entries)
    unless original == checked do throw (IO.userError "source/structural dictionary shape")
    for key in List.range 11 do
      unless sameOutcome (source.ref original (Int.ofNat key)) (certified.ref checked (Int.ofNat key)) do
        throw (IO.userError "source/structural dictionary observation")
      writes := writes+1
  for base in List.range 16 do
    let initial : DictionaryRecord Int Int := DictionaryRecord.fromOrder OrderOps.integer
    let first : SlotBody Int Int := fun _ _ => .ok (Int.ofNat base)
    let increment : SlotBody Int Int := fun _ old => do
      let some value ← old.get | throw "missing parent"
      return value+1
    let sum : SlotBody Int Int := fun self _ => do
      let some value ← self 1 | throw "missing self"
      return value+2
    let failure : SlotBody Int Int := fun _ _ => .error "slot failure"
    let dl := DelayedProto.compose (DictionaryRecord.semanticSlot 2 sum)
      (DelayedProto.compose (DictionaryRecord.semanticSlot 1 increment)
        (DelayedProto.compose (DictionaryRecord.semanticSlot 3 failure) (DictionaryRecord.semanticSlot 1 first)))
    let fl := DelayedProto.compose (FunctionRecord.semanticSlot 2 sum)
      (DelayedProto.compose (FunctionRecord.semanticSlot 1 increment)
        (DelayedProto.compose (FunctionRecord.semanticSlot 3 failure) (FunctionRecord.semanticSlot 1 first)))
    let dr := DictionaryRecord.instantiate dl initial
    let fr := (DelayedProto.instantiate fl (Thunk.pure Record.empty)).get
    for key in [0,1,2,3,4] do
      unless sameOutcome (dr.lookup key) (FunctionRecord.observe fr key) do
        throw (IO.userError "record representation observation/error")
  IO.println s!"CONSTRUCTION-SEMANTICS-OK dictionaryContexts=33 dictionaryReads={writes} recordContexts=16 recordReads=80"

#eval run
#print axioms Dictionary.bst_fixedPoint
#print axioms Dictionary.avl_fixedPoint
#print axioms Tree.fold_inorder
#print axioms Dictionary.avlNode_preserves
#print axioms Dictionary.avlNode_complete
#print axioms Tree.avl_insert_complete
#print axioms Tree.insert_sorted
#print axioms Tree.insert_entries
#print axioms Tree.search_insert
#print axioms Dictionary.avl_fromList
#print axioms Dictionary.merge_inorder
#print axioms OrderOps.integer_source
#print axioms OrderOps.integer_laws
#print axioms semanticSlot_related
#print axioms LayersRelated.compose
#print axioms KeyedPrototype.Definition.withKeys_values
#print axioms KeyedPrototype.Definition.withKeys_keys
end LeanPoo.Tests.ConstructionSemantics

#print axioms LeanPoo.Prototype.KeyedPrototype.recordSlotGen_values
