import LeanPoo.Prototype.BinaryTreeSemantics
import LeanPoo.Functional.StatefulValidation
import LeanPoo.Functional.Requirements

/-! Certified use of the existing source AVL dictionary, with ordered writes,
folds and pure multi-key transitions. The supplied comparator laws justify
total lookup/insertion; no dictionary algorithm is replaced. -/
namespace LeanPoo.Functional
open Prototype
variable {Key Value : Type} [DecidableEq Key]

structure OrderedDictionary (order : OrderOps Key) (lt : Key → Key → Prop) (Value : Type) where
  tree : Tree Key Value
  lawful : order.Laws lt
  balanced : tree.ValidAVL
  sorted : tree.Sorted lt

namespace OrderedDictionary
variable {order : OrderOps Key} {lt : Key → Key → Prop}

def empty (order : OrderOps Key) (lt : Key → Key → Prop) (laws : order.Laws lt) :
    OrderedDictionary order lt Value := ⟨.empty, laws, trivial, by simp [Tree.Sorted, Tree.inorder]⟩

/-- Lookup is the existing source method. Its unreachable comparator-error
branch is excluded by the retained ordering and comparator laws. -/
def get (dictionary : OrderedDictionary order lt Value) (key : Key) : Option Value :=
  match (Dictionary.avl (Acc := Unit) order).ref dictionary.tree key with
  | .error _ => none
  | .ok answer => answer

omit [DecidableEq Key] in
theorem get_source (dictionary : OrderedDictionary order lt Value) (key : Key) :
    (Dictionary.avl (Acc := Unit) order).ref dictionary.tree key = .ok (dictionary.get key) := by
  obtain ⟨answer, found, _⟩ := dictionary.tree.search_spec order lt dictionary.lawful key dictionary.sorted
  simp only [get, Dictionary.avl, Dictionary.structural, found]

omit [DecidableEq Key] in
theorem get_membership (dictionary : OrderedDictionary order lt Value) (key : Key) (value : Value) :
    dictionary.get key = some value ↔ (key, value) ∈ dictionary.tree.inorder := by
  obtain ⟨answer, found, members⟩ := dictionary.tree.search_spec order lt dictionary.lawful key dictionary.sorted
  have same : answer = dictionary.get key := Except.ok.inj (found.symm.trans (dictionary.get_source key))
  simpa only [same] using members value

/-- Ordered functional overwrites are the public observation model. -/
def writeView (view : Key → Option Value) (entry : Key × Value) : Key → Option Value :=
  fun query => if query = entry.1 then some entry.2 else view query

private def buildTree (dictionary : OrderedDictionary order lt Value) (entries : List (Key × Value)) :=
  entries.foldlM (fun tree entry => (Dictionary.avl (Acc := Unit) order).acons entry.1 entry.2 tree)
    dictionary.tree

private theorem buildTree_complete (dictionary : OrderedDictionary order lt Value)
    (entries : List (Key × Value)) :
    ∃ tree, buildTree dictionary entries = .ok tree ∧ tree.ValidAVL ∧ tree.Sorted lt ∧
      ∀ query, (Dictionary.avl (Acc := Unit) order).ref tree query =
        (entries.foldl Dictionary.updateView ((Dictionary.avl (Acc := Unit) order).ref dictionary.tree)) query :=
  Dictionary.avl_build order lt dictionary.lawful entries dictionary.tree dictionary.balanced dictionary.sorted

private theorem buildTree_valid (dictionary : OrderedDictionary order lt Value)
    (entries : List (Key × Value)) (tree : Tree Key Value)
    (built : buildTree dictionary entries = .ok tree) : tree.ValidAVL ∧ tree.Sorted lt := by
  obtain ⟨actual, completed, balanced, sorted, _⟩ := buildTree_complete dictionary entries
  have same := Except.ok.inj (completed.symm.trans built)
  subst actual
  exact ⟨balanced, sorted⟩

/-- Execute the actual inherited acons method in caller order. Completeness
removes structural refusal for this certified input; overwritten keys do not
accumulate duplicate entries. The original snapshot remains available. -/
def writeMany (dictionary : OrderedDictionary order lt Value) (entries : List (Key × Value)) :
    OrderedDictionary order lt Value :=
  match built : buildTree dictionary entries with
  | .error error => False.elim (by
      obtain ⟨tree, completed, _⟩ := buildTree_complete dictionary entries
      rw [built] at completed
      contradiction)
  | .ok tree =>
    let valid := buildTree_valid dictionary entries tree built
    ⟨tree, dictionary.lawful, valid.1, valid.2⟩

theorem writeMany_source (dictionary : OrderedDictionary order lt Value) (entries : List (Key × Value)) :
    entries.foldlM (fun tree entry => (Dictionary.avl (Acc := Unit) order).acons entry.1 entry.2 tree)
      dictionary.tree = .ok (dictionary.writeMany entries).tree := by
  unfold writeMany
  split <;> rename_i built
  · obtain ⟨tree, completed, _⟩ := buildTree_complete dictionary entries
    rw [built] at completed
    contradiction
  · exact built

private theorem writeViews (entries : List (Key × Value)) (view : Key → Option Value) :
    entries.foldl Dictionary.updateView (fun query => .ok (view query)) =
      fun query => .ok ((entries.foldl writeView view) query) := by
  induction entries generalizing view with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have one : Dictionary.updateView (fun query => .ok (view query)) entry =
        fun query => .ok (writeView view entry query) := by
      funext query
      simp only [Dictionary.updateView, writeView]
      split <;> rfl
    rw [one, ih]

/-- Complete lookup equality at every key, including absent keys, duplicates
and the exact caller order. Tree shape is deliberately absent from this law. -/
theorem get_writeMany (dictionary : OrderedDictionary order lt Value) (entries : List (Key × Value))
    (query : Key) :
    (dictionary.writeMany entries).get query = (entries.foldl writeView dictionary.get) query := by
  obtain ⟨tree, built, _, _, lookup⟩ := buildTree_complete dictionary entries
  have same := Except.ok.inj (built.symm.trans (dictionary.writeMany_source entries))
  subst tree
  have base : (Dictionary.avl (Acc := Unit) order).ref dictionary.tree =
      fun query => .ok (dictionary.get query) := funext dictionary.get_source
  have observed := lookup query
  rw [base, writeViews, (dictionary.writeMany entries).get_source] at observed
  exact Except.ok.inj observed

theorem get_writeMany_append (dictionary : OrderedDictionary order lt Value)
    (left right : List (Key × Value)) (query : Key) :
    (dictionary.writeMany (left ++ right)).get query =
      ((dictionary.writeMany left).writeMany right).get query := by
  rw [get_writeMany, get_writeMany, List.foldl_append]
  have before : (dictionary.writeMany left).get = left.foldl writeView dictionary.get :=
    funext (dictionary.get_writeMany left)
  rw [before]

theorem get_writeMany_other (dictionary : OrderedDictionary order lt Value)
    (entries : List (Key × Value)) (query : Key)
    (untouched : ∀ entry ∈ entries, query ≠ entry.1) :
    (dictionary.writeMany entries).get query = dictionary.get query := by
  rw [get_writeMany]
  have frame : ∀ (view : Key → Option Value), (entries.foldl writeView view) query = view query := by
    induction entries with
    | nil => intro view; rfl
    | cons entry rest ih =>
      intro view
      rw [List.foldl_cons, ih (fun e h => untouched e (by simp [h]))]
      simp [writeView, untouched entry (by simp)]
  exact frame dictionary.get

/-- Existing afoldr visits left/root/right; export retains that exact order. -/
def fold {Acc : Type} (dictionary : OrderedDictionary order lt Value) (combine : Key → Value → Acc → Acc)
    (initial : Acc) : Acc :=
  (Dictionary.avl order).afoldr combine initial dictionary.tree

omit [DecidableEq Key] in
theorem fold_inorder {Acc : Type} (dictionary : OrderedDictionary order lt Value)
    (combine : Key → Value → Acc → Acc) (initial : Acc) :
    dictionary.fold combine initial =
      dictionary.tree.inorder.foldl (fun acc entry => combine entry.1 entry.2 acc) initial :=
  dictionary.tree.fold_inorder combine initial

private theorem fold_bind {State Input Error : Type} (step : State → Input → Except Error State)
    (items : List Input) (state : Except Error State) :
    items.foldl (fun result item => result.bind (fun current => step current item)) state =
      state.bind (fun current => items.foldlM step current) := by
  induction items generalizing state with
  | nil => cases state <;> rfl
  | cons item rest ih =>
    rw [List.foldl_cons, ih]
    cases state with
    | error error => rfl
    | ok current =>
      simp only [Except.bind, List.foldlM_cons, bind]

/-- Fold the overriding dictionary's actual source traversal into the base.
Only its stored entries are forced; factory-valued entries remain functions. -/
def merge (dictionary overrides : OrderedDictionary order lt Value) : OrderedDictionary order lt Value :=
  dictionary.writeMany overrides.tree.inorder

theorem merge_source (dictionary overrides : OrderedDictionary order lt Value) :
    (Dictionary.avl (Acc := Except String (Tree Key Value)) order).merge overrides.tree dictionary.tree =
      .ok (dictionary.merge overrides).tree := by
  change (Dictionary.structural (Acc := Except String (Tree Key Value)) order Dictionary.avlNode).merge
    overrides.tree dictionary.tree = _
  rw [Dictionary.merge_inorder order Dictionary.avlNode]
  have folded := fold_bind
    (fun tree (entry : Key × Value) =>
      (Dictionary.avl (Acc := Except String (Tree Key Value)) order).acons entry.1 entry.2 tree)
    overrides.tree.inorder (.ok dictionary.tree)
  have built := dictionary.writeMany_source overrides.tree.inorder
  apply Eq.trans ?_ built
  simpa only [Dictionary.avl, Dictionary.structural, bind, Except.bind] using folded

theorem get_merge (dictionary overrides : OrderedDictionary order lt Value) (query : Key) :
    (dictionary.merge overrides).get query =
      (overrides.tree.inorder.foldl writeView dictionary.get) query :=
  dictionary.get_writeMany overrides.tree.inorder query

/-- Homogeneous factory-valued dictionaries become ordinary Functional
providers. Preparation selects functions; it does not execute their bodies. -/
def provider {Context : Type} {Result : Context → Type}
    (dictionary : OrderedDictionary order lt (Factory Context Result)) :
    Provider Context Key (fun context _ => Result context) := dictionary.get

/-- Complete capability preparation equals the functional overwrite model,
including first missing keys and repeated requested keys. -/
theorem prepare_writeMany {Context : Type} {Result : Context → Type}
    (dictionary : OrderedDictionary order lt (Factory Context Result))
    (entries : List (Key × Factory Context Result)) (keys : List Key) :
    Requirements.prepare (dictionary.writeMany entries).provider keys =
      Requirements.prepare (entries.foldl writeView dictionary.get) keys := by
  apply Requirements.prepare_congr
  intro key _
  exact dictionary.get_writeMany entries key

/-- A pure callback reads the complete current view and proposes ordered
multi-key writes. Refusal publishes no prefix; success returns those writes
and the actual certified AVL snapshot containing them. -/
def transact {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (input : Input) :
    Except Error (List (Key × Value)) × OrderedDictionary order lt Value :=
  match prepare dictionary.get input with
  | .error error => (.error error, dictionary)
  | .ok entries => (.ok entries, dictionary.writeMany entries)

theorem transact_error {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (input : Input)
    (error : Error) (failed : prepare dictionary.get input = .error error) :
    dictionary.transact prepare input = (.error error, dictionary) := by
  simp [transact, failed]

def transactView {Input Error : Type} (view : Key → Option Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (input : Input) :
    Except Error (List (Key × Value)) × (Key → Option Value) :=
  match prepare view input with
  | .error error => (.error error, view)
  | .ok entries => (.ok entries, entries.foldl writeView view)

/-- Full outcome and every retained lookup agree with ordinary functional
state, on both success and refusal. This does not infer host callback effects. -/
theorem transact_view {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (input : Input) :
    ((dictionary.transact prepare input).1, (dictionary.transact prepare input).2.get) =
      transactView dictionary.get prepare input := by
  unfold transact transactView
  cases prepare dictionary.get input with
  | error error => rfl
  | ok entries =>
    have same := funext (dictionary.get_writeMany entries)
    simp only [same]

def transactBatch {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (inputs : List Input) :=
  Validation.traverseState (fun state input => state.transact prepare input) dictionary inputs

theorem transactBatch_view {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value))) (inputs : List Input) :
    ((dictionary.transactBatch prepare inputs).1, (dictionary.transactBatch prepare inputs).2.get) =
      Validation.traverseState (fun view input => transactView view prepare input) dictionary.get inputs := by
  unfold transactBatch
  exact Validation.traverseState_transport (fun (state : OrderedDictionary order lt Value) input => state.transact prepare input)
    (fun view input => transactView view prepare input) get (fun state input => state.transact_view prepare input)
    dictionary inputs

theorem transactBatch_error_iff {Input Error : Type} (dictionary : OrderedDictionary order lt Value)
    (prepare : (Key → Option Value) → Input → Except Error (List (Key × Value)))
    (inputs : List Input) (error : Error) (final : OrderedDictionary order lt Value) :
    dictionary.transactBatch prepare inputs = (.error error, final) ↔
      ∃ before item after outputs next, inputs = before ++ item :: after ∧
        dictionary.transactBatch prepare before = (.ok outputs, next) ∧
        next.transact prepare item = (.error error, final) :=
  Validation.traverseState_error_iff _ dictionary inputs error final

end OrderedDictionary
end LeanPoo.Functional
