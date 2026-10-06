import LeanPoo.Prototype.Order

/-! The POOF binary-tree dictionary. Recursive methods dispatch through final
self; replacing only node construction can therefore rebalance every insert. -/
namespace LeanPoo.Prototype
variable {Key Value Acc : Type}

inductive Tree (Key Value : Type) where
  | empty
  | node (left : Tree Key Value) (key : Key) (value : Value)
      (height : Option Nat) (right : Tree Key Value)
deriving BEq, Repr

def Tree.isEmpty : Tree Key Value → Bool
  | .empty => true
  | .node .. => false

def Tree.size : Tree Key Value → Nat
  | .empty => 0
  | .node left _ _ _ right => left.size + 1 + right.size

def Tree.inorder : Tree Key Value → List (Key × Value)
  | .empty => []
  | .node left key value _ right => left.inorder ++ [(key,value)] ++ right.inorder

/-- Ordinary BST nodes have no height annotation; AVL nodes carry one. -/
def Tree.cachedHeight : Tree Key Value → Except String Nat
  | .empty => .ok 0
  | .node _ _ _ (some height) _ => .ok height
  | .node _ _ _ none _ => .error "AVL node requires annotated children"

structure Dictionary (Key Value Acc : Type) where
  keyOrder : OrderOps Key
  empty : Tree Key Value := .empty
  node : Tree Key Value → Key → Value → Tree Key Value → Except String (Tree Key Value)
  singleton : Key → Value → Except String (Tree Key Value)
  acons : Key → Value → Tree Key Value → Except String (Tree Key Value)
  ref : Tree Key Value → Key → Except String (Option Value)
  afoldr : (Key → Value → Acc → Acc) → Acc → Tree Key Value → Acc

def Dictionary.emptyMethods (order : OrderOps Key) : Dictionary Key Value Acc :=
  { keyOrder := order
    node := fun _ _ _ _ => .error "node method unavailable"
    singleton := fun _ _ => .error "singleton method unavailable"
    acons := fun _ _ _ => .error "acons method unavailable"
    ref := fun _ _ => .error "ref method unavailable"
    afoldr := fun _ initial _ => initial }

def Dictionary.withOrder (order : OrderOps Key) :
    DelayedProto (Dictionary Key Value Acc) (Dictionary Key Value Acc) (Dictionary Key Value Acc) :=
  fun _ inherited => { inherited.get with keyOrder := order }

/-- The source algorithms call self.node, self.acons, self.ref and self.afoldr. -/
def Dictionary.binaryTree :
    DelayedProto (Dictionary Key Value Acc) (Dictionary Key Value Acc) (Dictionary Key Value Acc) :=
  fun self inherited => { inherited.get with
    node := fun left key value right => .ok (.node left key value none right)
    singleton := fun key value => self.get.node .empty key value .empty
    acons := fun key value tree => do
      match tree with
      | .empty => self.get.singleton key value
      | .node left oldKey oldValue _ right =>
        match ← self.get.keyOrder.compare key oldKey with
        | .eq => self.get.node left key value right
        | .lt => self.get.node (← self.get.acons key value left) oldKey oldValue right
        | .gt => self.get.node left oldKey oldValue (← self.get.acons key value right)
    ref := fun tree key => do
      match tree with
      | .empty => return none
      | .node left oldKey value _ right =>
        match ← self.get.keyOrder.compare key oldKey with
        | .eq => return some value
        | .lt => self.get.ref left key
        | .gt => self.get.ref right key
    -- Match the paper's afoldr accumulation order (left, root, then right).
    afoldr := fun combine initial tree =>
      match tree with
      | .empty => initial
      | .node left key value _ right =>
        self.get.afoldr combine (combine key value (self.get.afoldr combine initial left)) right }

unsafe def Dictionary.instantiate (order : OrderOps Key)
    (prototype : DelayedProto (Dictionary Key Value Acc) (Dictionary Key Value Acc) (Dictionary Key Value Acc)) :
    Dictionary Key Value Acc :=
  (DelayedProto.instantiate prototype (Thunk.pure (Dictionary.emptyMethods order))).get

def Dictionary.fromList (dictionary : Dictionary Key Value Acc) (entries : List (Key × Value)) :
    Except String (Tree Key Value) :=
  entries.foldlM (fun tree entry => dictionary.acons entry.1 entry.2 tree) dictionary.empty

/-- Source Dict->alist: prepend while folding left/root/right. -/
def Dictionary.toList (dictionary : Dictionary Key Value (List (Key × Value)))
    (tree : Tree Key Value) : List (Key × Value) :=
  dictionary.afoldr (fun key value result => (key,value) :: result) [] tree

/-- Source Dict-merge: override entries win over the retained base. The fold
accumulator carries explicit insertion errors, using inherited acons. -/
def Dictionary.merge (dictionary : Dictionary Key Value (Except String (Tree Key Value)))
    (overrideTree baseTree : Tree Key Value) : Except String (Tree Key Value) :=
  dictionary.afoldr (fun key value result => do dictionary.acons key value (← result))
    (.ok baseTree) overrideTree

end LeanPoo.Prototype
