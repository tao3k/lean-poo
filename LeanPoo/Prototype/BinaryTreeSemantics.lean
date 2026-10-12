import LeanPoo.Prototype.AVLSemantics

/-! Structural solutions of the paper's recursive dictionary methods. The
one-unfolding equations connect these solutions to the actual open prototype;
ordering laws are explicit assumptions on its replaceable comparison method. -/
namespace LeanPoo.Prototype
variable {Key Value Acc : Type}

structure OrderOps.Laws (order : OrderOps Key) (lt : Key → Key → Prop) : Prop where
  total : ∀ x y, ∃ result, order.compare x y = .ok result
  equal : ∀ x y, order.compare x y = .ok .eq ↔ x = y
  less : ∀ x y, order.compare x y = .ok .lt ↔ lt x y
  greater : ∀ x y, order.compare x y = .ok .gt ↔ lt y x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  irrefl : ∀ x, ¬lt x x

def Tree.insert (compare : Key → Key → Except String Ordering)
    (node : Tree Key Value → Key → Value → Tree Key Value → Except String (Tree Key Value))
    (key : Key) (value : Value) : Tree Key Value → Except String (Tree Key Value)
  | .empty => node .empty key value .empty
  | .node left oldKey oldValue _ right => do
    match ← compare key oldKey with
    | .eq => node left key value right
    | .lt => node (← left.insert compare node key value) oldKey oldValue right
    | .gt => node left oldKey oldValue (← right.insert compare node key value)

def Tree.search (compare : Key → Key → Except String Ordering)
    (key : Key) : Tree Key Value → Except String (Option Value)
  | .empty => .ok none
  | .node left oldKey value _ right => do
    match ← compare key oldKey with
    | .eq => return some value
    | .lt => left.search compare key
    | .gt => right.search compare key

def Tree.fold (combine : Key → Value → Acc → Acc) (initial : Acc) : Tree Key Value → Acc
  | .empty => initial
  | .node left key value _ right => right.fold combine (combine key value (left.fold combine initial))

def Dictionary.structural (order : OrderOps Key)
    (node : Tree Key Value → Key → Value → Tree Key Value → Except String (Tree Key Value)) :
    Dictionary Key Value Acc :=
  { keyOrder := order, node, singleton := fun key value => node .empty key value .empty
    acons := Tree.insert order.compare node
    ref := fun tree key => tree.search order.compare key
    afoldr := Tree.fold }

def Dictionary.bst (order : OrderOps Key) : Dictionary Key Value Acc :=
  structural order (fun left key value right => .ok (.node left key value none right))

def Dictionary.avl (order : OrderOps Key) : Dictionary Key Value Acc :=
  structural order Dictionary.avlNode

theorem Dictionary.structural_insert (order : OrderOps Key) (node) (key : Key) (value : Value)
    (tree : Tree Key Value) :
    (structural (Acc := Acc) order node).insertStep key value tree =
      (structural (Acc := Acc) order node).acons key value tree := by
  cases tree <;> rfl

theorem Dictionary.structural_ref (order : OrderOps Key) (node) (key : Key)
    (tree : Tree Key Value) :
    (structural (Acc := Acc) order node).refStep tree key =
      (structural (Acc := Acc) order node).ref tree key := by
  cases tree <;> rfl

theorem Dictionary.structural_fold (order : OrderOps Key) (node)
    (combine : Key → Value → Acc → Acc) (initial : Acc) (tree : Tree Key Value) :
    (structural order node).foldStep combine initial tree =
      (structural order node).afoldr combine initial tree := by
  cases tree <;> rfl

/-- Both closed dictionaries satisfy the exact source prototype equations. -/
theorem Dictionary.bst_fixedPoint (order : OrderOps Key) :
    binaryTree (Thunk.pure (bst (Value := Value) (Acc := Acc) order))
      (Thunk.pure (emptyMethods order)) = bst order := by
  apply Dictionary.ext <;> try rfl
  · funext key value tree; exact structural_insert order _ key value tree
  · funext tree key; exact structural_ref order _ key tree
  · funext combine initial tree; exact structural_fold order _ combine initial tree

theorem Dictionary.avl_fixedPoint (order : OrderOps Key) :
    (DelayedProto.compose avlRebalance binaryTree)
      (Thunk.pure (avl (Value := Value) (Acc := Acc) order))
      (Thunk.pure (emptyMethods order)) = avl order := by
  apply Dictionary.ext <;> try rfl
  · funext key value tree; exact structural_insert order _ key value tree
  · funext tree key; exact structural_ref order _ key tree
  · funext combine initial tree; exact structural_fold order _ combine initial tree

theorem Tree.fold_inorder (tree : Tree Key Value) (combine : Key → Value → Acc → Acc)
    (initial : Acc) : tree.fold combine initial =
      tree.inorder.foldl (fun acc entry => combine entry.1 entry.2 acc) initial := by
  induction tree generalizing initial with
  | empty => rfl
  | node left key value cached right ihl ihr =>
    simp [fold, inorder, List.foldl_append, ihl, ihr]

def Tree.Sorted (lt : Key → Key → Prop) (tree : Tree Key Value) : Prop :=
  tree.inorder.Pairwise (fun x y => lt x.1 y.1)

def Tree.Keys (predicate : Key → Prop) (tree : Tree Key Value) : Prop :=
  ∀ entry ∈ tree.inorder, predicate entry.1

theorem Tree.sorted_parts (lt : Key → Key → Prop) (left right : Tree Key Value)
    (key : Key) (value : Value) (cached : Option Nat)
    (sorted : (node left key value cached right).Sorted lt) :
    left.Sorted lt ∧ right.Sorted lt ∧ left.Keys (lt · key) ∧ right.Keys (lt key ·) := by
  have parts := List.pairwise_append.mp sorted
  have lhs := List.pairwise_append.mp parts.1
  refine ⟨lhs.1, parts.2.1, ?_, ?_⟩
  · intro entry member; exact lhs.2.2 entry member (key,value) (by simp)
  · intro entry member; exact parts.2.2 (key,value) (by simp) entry member

theorem Tree.sorted_join (lt : Key → Key → Prop)
    (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (left right : Tree Key Value) (key : Key) (value : Value)
    (sl : left.Sorted lt) (sr : right.Sorted lt)
    (bl : left.Keys (lt · key)) (br : right.Keys (lt key ·)) :
    (left.inorder ++ [(key,value)] ++ right.inorder).Pairwise (fun x y => lt x.1 y.1) := by
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨sl, by simp, ?_⟩, sr, ?_⟩
  · intro a ha b hb
    have same : b = (key,value) := by simpa using hb
    subst b; exact bl a ha
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · exact trans (bl a ha) (br b hb)
    · have same : a = (key,value) := by simpa using ha
      subst a; exact br b hb

def NodeContents (node : Tree Key Value → Key → Value → Tree Key Value → Except String (Tree Key Value)) : Prop :=
  ∀ left key value right output, node left key value right = .ok output →
    output.inorder = left.inorder ++ [(key,value)] ++ right.inorder

theorem Tree.insert_keys (compare) (node) (contents : NodeContents (Key := Key) (Value := Value) node)
    (tree output : Tree Key Value) (key : Key) (value : Value)
    (success : tree.insert compare node key value = .ok output) :
    ∀ entry ∈ output.inorder, entry.1 = key ∨ entry ∈ tree.inorder := by
  induction tree generalizing output with
  | empty =>
    rw [insert] at success
    simp [contents _ _ _ _ _ success, inorder]
  | node left oldKey oldValue cached right ihl ihr =>
    simp only [insert] at success
    cases result : compare key oldKey with
    | error message => simp [result, bind, Except.bind] at success
    | ok ordering =>
      cases ordering with
      | eq =>
        simp only [result, bind, Except.bind] at success
        intro entry member
        rw [contents _ _ _ _ _ success] at member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with (member | same) | member
        · exact Or.inr (by simp [inorder, member])
        · subst entry; exact Or.inl rfl
        · exact Or.inr (by simp [inorder, member])
      | lt =>
        cases child : left.insert compare node key value with
        | error message => simp [result, child, bind, Except.bind] at success
        | ok next =>
          simp only [result, child, bind, Except.bind] at success
          intro entry member
          rw [contents _ _ _ _ _ success] at member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with (member | same) | member
          · rcases ihl next child entry member with same | old
            · exact Or.inl same
            · exact Or.inr (by simp [inorder, old])
          · subst entry; exact Or.inr (by simp [inorder])
          · exact Or.inr (by simp [inorder, member])
      | gt =>
        cases child : right.insert compare node key value with
        | error message => simp [result, child, bind, Except.bind] at success
        | ok next =>
          simp only [result, child, bind, Except.bind] at success
          intro entry member
          rw [contents _ _ _ _ _ success] at member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with (member | same) | member
          · exact Or.inr (by simp [inorder, member])
          · subst entry; exact Or.inr (by simp [inorder])
          · rcases ihr next child entry member with same | old
            · exact Or.inl same
            · exact Or.inr (by simp [inorder, old])

theorem Tree.insert_sorted (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (node) (contents : NodeContents (Key := Key) (Value := Value) node)
    (tree output : Tree Key Value) (key : Key) (value : Value)
    (sorted : tree.Sorted lt) (success : tree.insert order.compare node key value = .ok output) :
    output.Sorted lt := by
  induction tree generalizing output with
  | empty =>
    rw [insert] at success
    simp [Sorted, contents _ _ _ _ _ success, inorder]
  | node left oldKey oldValue cached right ihl ihr =>
    obtain ⟨sl,sr,bl,br⟩ := sorted_parts lt left right oldKey oldValue cached sorted
    obtain ⟨result, comparison⟩ := laws.total key oldKey
    simp only [insert, comparison, bind, Except.bind] at success
    cases result with
    | eq =>
      have same := (laws.equal key oldKey).mp comparison
      subst oldKey
      rw [Sorted, contents _ _ _ _ _ success]
      exact sorted_join lt laws.trans left right key value sl sr bl br
    | lt =>
      have less := (laws.less key oldKey).mp comparison
      cases child : left.insert order.compare node key value with
      | error message => simp [child, bind, Except.bind] at success
      | ok next =>
        simp only [child, bind, Except.bind] at success
        rw [Sorted, contents _ _ _ _ _ success]
        apply sorted_join lt laws.trans next right oldKey oldValue (ihl next sl child) sr _ br
        intro entry member
        rcases insert_keys order.compare node contents left next key value child entry member with same | old
        · simpa [same] using less
        · exact bl entry old
    | gt =>
      have greater := (laws.greater key oldKey).mp comparison
      cases child : right.insert order.compare node key value with
      | error message => simp [child, bind, Except.bind] at success
      | ok next =>
        simp only [child, bind, Except.bind] at success
        rw [Sorted, contents _ _ _ _ _ success]
        apply sorted_join lt laws.trans left next oldKey oldValue sl (ihr next sr child) bl _
        intro entry member
        rcases insert_keys order.compare node contents right next key value child entry member with same | old
        · simpa [same] using greater
        · exact br entry old

/-- Arbitrary legal AVL insertion succeeds, retains every height annotation,
and changes total height by either zero or one. No enumeration bound is used. -/
theorem Tree.avl_insert_complete (order : OrderOps Key)
    (total : ∀ x y, ∃ result, order.compare x y = .ok result)
    (tree : Tree Key Value) (key : Key) (value : Value) (valid : tree.ValidAVL) :
    ∃ output, tree.insert order.compare Dictionary.avlNode key value = .ok output ∧
      output.ValidAVL ∧ tree.height ≤ output.height ∧ output.height ≤ tree.height+1 := by
  induction tree with
  | empty =>
    obtain ⟨output, success, lower, upper, balanced⟩ :=
      Dictionary.avlNode_complete (.empty : Tree Key Value) .empty key value trivial trivial (by simp [height]) (by simp [height])
    refine ⟨output, success, (Dictionary.avlNode_preserves .empty .empty output key value trivial trivial success).1, ?_⟩
    simp only [height] at lower upper ⊢; omega
  | node left oldKey oldValue cached right ihl ihr =>
    obtain ⟨vl,vr,hcache,bl,br⟩ := valid
    obtain ⟨result, comparison⟩ := total key oldKey
    cases result with
    | eq =>
      obtain ⟨output, success, lower, upper, balanced⟩ :=
        Dictionary.avlNode_complete left right key value vl vr (by omega) (by omega)
      refine ⟨output, by simp [insert, comparison, bind, Except.bind, success],
        (Dictionary.avlNode_preserves _ _ _ _ _ vl vr success).1, ?_⟩
      have exactHeight := balanced bl br
      simp only [height]; omega
    | lt =>
      obtain ⟨next, child, vn, low, high⟩ := ihl vl
      obtain ⟨output, success, lower, upper, balanced⟩ :=
        Dictionary.avlNode_complete next right oldKey oldValue vn vr (by omega) (by omega)
      refine ⟨output, by simp [insert, comparison, child, bind, Except.bind, success],
        (Dictionary.avlNode_preserves _ _ _ _ _ vn vr success).1, ?_⟩
      simp only [height]
      by_cases a : next.height ≤ right.height+1
      · have b : right.height ≤ next.height+1 := by omega
        have exactHeight := balanced a b
        omega
      · omega
    | gt =>
      obtain ⟨next, child, vn, low, high⟩ := ihr vr
      obtain ⟨output, success, lower, upper, balanced⟩ :=
        Dictionary.avlNode_complete left next oldKey oldValue vl vn (by omega) (by omega)
      refine ⟨output, by simp [insert, comparison, child, bind, Except.bind, success],
        (Dictionary.avlNode_preserves _ _ _ _ _ vl vn success).1, ?_⟩
      simp only [height]
      by_cases b : next.height ≤ left.height+1
      · have a : left.height ≤ next.height+1 := by omega
        have exactHeight := balanced a b
        omega
      · omega

theorem Tree.avl_insert_sorted (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (tree output : Tree Key Value) (key : Key) (value : Value)
    (sorted : tree.Sorted lt)
    (success : tree.insert order.compare Dictionary.avlNode key value = .ok output) :
    output.Sorted lt :=
  insert_sorted order lt laws _ (fun l k v r o h => Dictionary.avlNode_contents l r o k v h) tree output key value sorted success

theorem Tree.search_spec (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (tree : Tree Key Value) (key : Key) (sorted : tree.Sorted lt) :
    ∃ answer, tree.search order.compare key = .ok answer ∧
      ∀ value, answer = some value ↔ (key,value) ∈ tree.inorder := by
  induction tree with
  | empty => exact ⟨none,rfl,by simp [inorder]⟩
  | node left oldKey oldValue cached right ihl ihr =>
    obtain ⟨sl,sr,bl,br⟩ := sorted_parts lt left right oldKey oldValue cached sorted
    obtain ⟨result, comparison⟩ := laws.total key oldKey
    cases result with
    | eq =>
      have same := (laws.equal key oldKey).mp comparison
      subst oldKey
      have nl (value : Value) : (key,value) ∉ left.inorder :=
        fun member => laws.irrefl key (bl (key,value) member)
      have nr (value : Value) : (key,value) ∉ right.inorder :=
        fun member => laws.irrefl key (br (key,value) member)
      refine ⟨some oldValue, by simp [search, comparison, bind, Except.bind, pure, Except.pure], ?_⟩
      intro value; simp [inorder, nl, nr, eq_comm]
    | lt =>
      have less := (laws.less key oldKey).mp comparison
      have ne : key ≠ oldKey := by intro same; subst oldKey; exact laws.irrefl key less
      have nr (value : Value) : (key,value) ∉ right.inorder :=
        fun member => laws.irrefl key (laws.trans less (br (key,value) member))
      obtain ⟨answer, found, correct⟩ := ihl sl
      refine ⟨answer, by simp [search, comparison, found, bind, Except.bind], ?_⟩
      intro value; simpa [inorder, ne, nr] using correct value
    | gt =>
      have greater := (laws.greater key oldKey).mp comparison
      have ne : key ≠ oldKey := by intro same; subst oldKey; exact laws.irrefl key greater
      have nl (value : Value) : (key,value) ∉ left.inorder :=
        fun member => laws.irrefl key (laws.trans (bl (key,value) member) greater)
      obtain ⟨answer, found, correct⟩ := ihr sr
      refine ⟨answer, by simp [search, comparison, found, bind, Except.bind], ?_⟩
      intro value; simpa [inorder, ne, nl] using correct value

/-- Exact overwrite and frame law for every stored value, including thunks. -/
theorem Tree.insert_entries [DecidableEq Key] (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (node) (contents : NodeContents (Key := Key) (Value := Value) node)
    (tree output : Tree Key Value) (key : Key) (value : Value)
    (sorted : tree.Sorted lt) (success : tree.insert order.compare node key value = .ok output) :
    ∀ query result, (query,result) ∈ output.inorder ↔
      if query = key then result = value else (query,result) ∈ tree.inorder := by
  induction tree generalizing output with
  | empty =>
    rw [insert] at success
    intro query result
    by_cases same : query = key
    · simp [contents _ _ _ _ _ success, inorder, same, eq_comm]
    · simp [contents _ _ _ _ _ success, inorder, same, Ne.symm same]
  | node left oldKey oldValue cached right ihl ihr =>
    obtain ⟨sl,sr,bl,br⟩ := sorted_parts lt left right oldKey oldValue cached sorted
    obtain ⟨ordering, comparison⟩ := laws.total key oldKey
    simp only [insert, comparison, bind, Except.bind] at success
    cases ordering with
    | eq =>
      have same := (laws.equal key oldKey).mp comparison
      subst oldKey
      have nl (result : Value) : (key,result) ∉ left.inorder :=
        fun member => laws.irrefl key (bl (key,result) member)
      have nr (result : Value) : (key,result) ∉ right.inorder :=
        fun member => laws.irrefl key (br (key,result) member)
      intro query result
      by_cases same : query = key
      · subst query; simp [contents _ _ _ _ _ success, nl, nr, eq_comm]
      · simp [contents _ _ _ _ _ success, inorder, same]
    | lt =>
      have less := (laws.less key oldKey).mp comparison
      have ne : key ≠ oldKey := by intro same; subst oldKey; exact laws.irrefl key less
      have nr (result : Value) : (key,result) ∉ right.inorder :=
        fun member => laws.irrefl key (laws.trans less (br (key,result) member))
      cases child : left.insert order.compare node key value with
      | error message => simp [child, bind, Except.bind] at success
      | ok next =>
        simp only [child, bind, Except.bind] at success
        intro query result
        have correct := ihl next sl child query result
        by_cases same : query = key
        · subst query; simpa [contents _ _ _ _ _ success, ne, nr, eq_comm] using correct
        · simpa [contents _ _ _ _ _ success, inorder, same, or_assoc] using
            (show ((query,result) ∈ next.inorder ∨ (query,result) = (oldKey,oldValue)) ∨
                (query,result) ∈ right.inorder ↔
              ((query,result) ∈ left.inorder ∨ (query,result) = (oldKey,oldValue)) ∨
                (query,result) ∈ right.inorder from by rw [correct]; simp [same])
    | gt =>
      have greater := (laws.greater key oldKey).mp comparison
      have ne : key ≠ oldKey := by intro same; subst oldKey; exact laws.irrefl key greater
      have nl (result : Value) : (key,result) ∉ left.inorder :=
        fun member => laws.irrefl key (laws.trans (bl (key,result) member) greater)
      cases child : right.insert order.compare node key value with
      | error message => simp [child, bind, Except.bind] at success
      | ok next =>
        simp only [child, bind, Except.bind] at success
        intro query result
        have correct := ihr next sr child query result
        by_cases same : query = key
        · subst query; simpa [contents _ _ _ _ _ success, ne, nl, eq_comm] using correct
        · simpa [contents _ _ _ _ _ success, inorder, same, or_assoc] using
            (show ((query,result) ∈ left.inorder ∨ (query,result) = (oldKey,oldValue)) ∨
                (query,result) ∈ next.inorder ↔
              ((query,result) ∈ left.inorder ∨ (query,result) = (oldKey,oldValue)) ∨
                (query,result) ∈ right.inorder from by rw [correct]; simp [same])

theorem Tree.bst_insert_complete (order : OrderOps Key)
    (total : ∀ x y, ∃ result, order.compare x y = .ok result)
    (tree : Tree Key Value) (key : Key) (value : Value) :
    ∃ output, tree.insert order.compare
      (fun left key value right => .ok (.node left key value none right)) key value = .ok output := by
  induction tree with
  | empty => exact ⟨_, rfl⟩
  | node left oldKey oldValue cached right ihl ihr =>
    obtain ⟨result, comparison⟩ := total key oldKey
    obtain ⟨nextLeft, hl⟩ := ihl
    obtain ⟨nextRight, hr⟩ := ihr
    cases result <;> simp [insert, comparison, hl, hr, bind, Except.bind]

/-- Inserting at one key changes exactly that lookup. -/
theorem Tree.search_insert [DecidableEq Key] (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (node) (contents : NodeContents (Key := Key) (Value := Value) node)
    (tree output : Tree Key Value) (key query : Key) (value : Value)
    (sorted : tree.Sorted lt) (success : tree.insert order.compare node key value = .ok output) :
    output.search order.compare query =
      if query = key then .ok (some value) else tree.search order.compare query := by
  have outputSorted := insert_sorted order lt laws node contents tree output key value sorted success
  obtain ⟨before, hb, sb⟩ := search_spec order lt laws tree query sorted
  obtain ⟨after, ha, sa⟩ := search_spec order lt laws output query outputSorted
  have changed := insert_entries order lt laws node contents tree output key value sorted success
  by_cases same : query = key
  · have equal : after = some value := (sa value).mpr ((changed query value).mpr (by simp [same]))
    rw [ha]; simp [same, equal]
  · have equal : after = before := Option.ext fun result => by
      rw [sa result, changed query result, if_neg same, ← sb result]
    simp [same, ha, hb, equal]

theorem Dictionary.avl_insert_lookup [DecidableEq Key] (order : OrderOps Key)
    (lt : Key → Key → Prop) (laws : order.Laws lt) (tree output : Tree Key Value)
    (key query : Key) (value : Value) (sorted : tree.Sorted lt)
    (success : (avl (Acc := Acc) order).acons key value tree = .ok output) :
    (avl (Acc := Acc) order).ref output query =
      if query = key then .ok (some value) else (avl (Acc := Acc) order).ref tree query :=
  Tree.search_insert order lt laws _ (fun l k v r o h => avlNode_contents l r o k v h)
    tree output key query value sorted success

/-- A total numeric order satisfying the paper's final-self mixin equation. -/
def OrderOps.integer : OrderOps Int :=
  { less := fun x y => decide (x < y), equal := (· == ·), greater := fun x y => decide (x > y)
    compare := fun x y => if decide (x < y) then .ok .lt
      else if decide (x > y) then .ok .gt
      else if x == y then .ok .eq else .error "incomparable" }

theorem OrderOps.integer_source :
    (DelayedProto.compose compareMixin number) (Thunk.pure integer) (Thunk.pure empty) = integer := rfl

theorem OrderOps.integer_laws : integer.Laws (· < ·) := by
  have comparison (x y : Int) : integer.compare x y =
      if x < y then .ok .lt else if y < x then .ok .gt else .ok .eq := by
    by_cases less : x < y
    · simp [integer, less]
    · by_cases greater : y < x
      · simp [integer, less, greater]
      · have same : x = y := by omega
        simp [integer, less, greater, same]
  constructor
  · intro x y
    by_cases a : x < y
    · exact ⟨.lt, by rw [comparison]; simp [a]⟩
    · by_cases b : y < x
      · exact ⟨.gt, by rw [comparison]; simp [a,b]⟩
      · exact ⟨.eq, by rw [comparison]; simp [a,b]⟩
  · intro x y; rw [comparison]
    by_cases a : x < y <;> by_cases b : y < x <;> simp [a,b]
    all_goals omega
  · intro x y; rw [comparison]
    by_cases a : x < y <;> by_cases b : y < x <;> simp [a,b]
  · intro x y; rw [comparison]
    by_cases a : x < y <;> by_cases b : y < x <;> simp [a,b]
    all_goals omega
  · intro x y z; omega
  · intro x; omega

def Dictionary.updateView [DecidableEq Key] (view : Key → Except String (Option Value))
    (entry : Key × Value) : Key → Except String (Option Value) :=
  fun query => if query = entry.1 then .ok (some entry.2) else view query

/-- Bulk construction preserves validity and equals ordered functional writes
at every key, including overwrites in arbitrary input lists. -/
theorem Dictionary.avl_build [DecidableEq Key] (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (entries : List (Key × Value)) (tree : Tree Key Value)
    (valid : tree.ValidAVL) (sorted : tree.Sorted lt) :
    ∃ output, entries.foldlM (fun current entry =>
      (avl (Acc := Acc) order).acons entry.1 entry.2 current) tree = .ok output ∧
      output.ValidAVL ∧ output.Sorted lt ∧
      ∀ query, (avl (Acc := Acc) order).ref output query =
        (entries.foldl updateView ((avl (Acc := Acc) order).ref tree)) query := by
  induction entries generalizing tree with
  | nil => exact ⟨tree,rfl,valid,sorted,fun _ => rfl⟩
  | cons entry rest ih =>
    obtain ⟨next, inserted, vn, _, _⟩ := tree.avl_insert_complete order laws.total entry.1 entry.2 valid
    have sn := tree.avl_insert_sorted order lt laws next entry.1 entry.2 sorted inserted
    obtain ⟨output, built, vo, so, lookup⟩ := ih next vn sn
    refine ⟨output, ?_, vo, so, ?_⟩
    · simp only [List.foldlM_cons, Dictionary.avl, Dictionary.structural, inserted, bind, Except.bind]
      exact built
    · have writes : (avl (Acc := Acc) order).ref next =
          updateView ((avl (Acc := Acc) order).ref tree) entry := by
        funext query; exact avl_insert_lookup order lt laws tree next entry.1 query entry.2 sorted inserted
      intro query
      simpa only [List.foldl_cons, ← writes] using lookup query

theorem Dictionary.avl_fromList [DecidableEq Key] (order : OrderOps Key)
    (lt : Key → Key → Prop) (laws : order.Laws lt) (entries : List (Key × Value)) :
    ∃ output, fromList (avl (Acc := Acc) order) entries = .ok output ∧
      output.ValidAVL ∧ output.Sorted lt ∧
      ∀ query, (avl (Acc := Acc) order).ref output query =
        (entries.foldl updateView (fun _ => .ok none)) query :=
  avl_build order lt laws entries .empty trivial (by simp [Tree.Sorted, Tree.inorder])

theorem Dictionary.merge_inorder (order : OrderOps Key) (node)
    (overrideTree baseTree : Tree Key Value) :
    merge (structural order node) overrideTree baseTree =
      overrideTree.inorder.foldl (fun result entry => do
        (structural (Acc := Except String (Tree Key Value)) order node).acons entry.1 entry.2 (← result))
        (.ok baseTree) :=
  Tree.fold_inorder overrideTree _ _

end LeanPoo.Prototype
