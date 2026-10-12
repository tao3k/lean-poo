import LeanPoo.Object.Multimethod
import Std.Data.HashMap.Lemmas

/-! The appendix B dispatch specification: enumerate specialization tuples
in lexicographic precedence order, retrieve each exact method group, and then
filter by the current arguments. Cache correctness is invariant under the
actual registration, lookup and eviction operations. -/
namespace LeanPoo.Object

namespace MethodIndex

def tuples : List (List Specializer) → List (List Specializer)
  | [] => [[]]
  | order :: rest => order.flatMap fun name => (tuples rest).map (name :: ·)

def reference (index : MethodIndex Method) (orders : List (List Specializer)) : List Method :=
  (tuples orders).flatMap index.lookup

private theorem push_fold (values : List Method) (found : Array Method) :
    (values.foldl (fun current method => current.push method) found).toList =
      found.toList ++ values := by
  induction values generalizing found with
  | nil => simp
  | cons value rest ih => simp [ih, Array.toList_push, List.append_assoc]

private theorem fold_collect (children : List (Specializer × MethodIndex Method))
    (rest : List (List Specializer))
    (correct : ∀ (child : MethodIndex Method) (found : Array Method),
      (child.collect rest found).toList = found.toList ++ child.reference rest)
    (order : List Specializer) (found : Array Method) :
    (order.foldl (fun current name =>
        (child? children name).elim current (fun child => child.collect rest current)) found).toList =
      found.toList ++ order.flatMap (fun name => match child? children name with
        | some child => child.reference rest | none => []) := by
  induction order generalizing found with
  | nil => simp
  | cons name tail ih =>
    cases child : child? children name with
    | none => simp [child, ih]
    | some value => simp [child, ih, correct, List.append_assoc]

theorem collect_reference (index : MethodIndex Method) (orders : List (List Specializer))
    (found : Array Method) :
    (index.collect orders found).toList = found.toList ++ index.reference orders := by
  induction orders generalizing index found with
  | nil => cases index with | node values children => simpa [collect, reference, tuples, lookup] using push_fold values found
  | cons order rest ih =>
    cases index with
    | node values children =>
      have loop := fold_collect children rest ih order found
      calc
        ((node values children).collect (order :: rest) found).toList =
            found.toList ++ order.flatMap (fun name => match child? children name with
              | some child => child.reference rest | none => []) := by
          simpa only [collect] using loop
        _ = found.toList ++ (node values children).reference (order :: rest) := by
          congr 1
          simp only [reference, tuples, List.flatMap_assoc, List.flatMap_map]
          congr 1
          funext name
          cases child : child? children name with
          | none => simp [lookup, child]
          | some value => simp [lookup, child, reference]

end MethodIndex

namespace MethodCandidate

def selected (args : Args) (candidate : MethodCandidate Args Method) : Option Method :=
  if candidate.applies args then some candidate.method else none

 theorem select_reference (candidates : Array (MethodCandidate Args Method)) (args : Args) :
    (select candidates args).toList = candidates.toList.filterMap (selected args) := by
  have loop (items : List (MethodCandidate Args Method)) (found : Array Method) :
      (items.foldl (fun current candidate =>
        if candidate.applies args then current.push candidate.method else current) found).toList =
      found.toList ++ items.filterMap (selected args) := by
    induction items generalizing found with
    | nil => simp
    | cons candidate rest ih =>
      simp only [List.foldl_cons, List.filterMap_cons, selected]
      split <;> simp_all [Array.toList_push, List.append_assoc]
  simpa only [select, ← Array.foldl_toList, Array.toList_empty, List.nil_append] using
    loop candidates.toList #[]

end MethodCandidate

namespace ShapeCache

def Sound (reference : DispatchShape → Value) (cache : ShapeCache Value) : Prop :=
  ∀ shape value, cache.get? shape = some value → value = reference shape

theorem sound_empty (reference : DispatchShape → Value) : Sound reference {} := by
  intro shape value found
  simp [get?, Std.HashMap.getElem?_empty] at found

private theorem erase_sound (reference : DispatchShape → Value)
    (values : Std.HashMap DispatchShape Value)
    (sound : ∀ shape value, values[shape]? = some value → value = reference shape)
    (stale : DispatchShape) :
    ∀ shape value, (values.erase stale)[shape]? = some value → value = reference shape := by
  intro shape value found
  rw [Std.HashMap.getElem?_erase] at found
  split at found
  · contradiction
  · exact sound shape value found

theorem sound_remember (reference : DispatchShape → Value) (cache : ShapeCache Value)
    (sound : Sound reference cache) (shape : DispatchShape) (value : Value)
    (correct : value = reference shape) : Sound reference (cache.remember shape value) := by
  have inserted : ∀ query item, (cache.values.insert shape value)[query]? = some item →
      item = reference query := by
    intro query item found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · rename_i same
      have equal : shape = query := by simpa using same
      cases equal
      exact (Option.some.inj found).symm.trans correct
    · exact sound query item found
  have erased (stales : List DispatchShape) :
      ∀ query item, (stales.foldl (fun current stale => current.erase stale)
        (cache.values.insert shape value))[query]? = some item → item = reference query := by
    have preserve (table : Std.HashMap DispatchShape Value)
        (valid : ∀ query item, table[query]? = some item → item = reference query) :
        ∀ query item, (stales.foldl (fun current stale => current.erase stale) table)[query]? =
          some item → item = reference query := by
      induction stales generalizing table with
      | nil => exact valid
      | cons stale rest ih => exact ih _ (erase_sound reference table valid stale)
    exact preserve _ inserted
  exact erased _

theorem sound_touch (reference : DispatchShape → Value) (cache : ShapeCache Value)
    (sound : Sound reference cache) (shape : DispatchShape) :
    Sound reference (cache.touch shape) := by
  unfold touch
  split
  · exact sound
  · cases found : cache.get? shape with
    | none => exact sound
    | some value => exact sound_remember reference cache sound shape value (sound shape value found)

end ShapeCache

def Multimethod.CacheSound (generic : Multimethod Args Method Result) : Prop :=
  generic.cache.Sound generic.candidatesFor

theorem Multimethod.cacheSound_of_empty (generic : Multimethod Args Method Result)
    (empty : generic.cache = {}) : generic.CacheSound := by
  unfold CacheSound
  rw [empty]
  exact ShapeCache.sound_empty _

theorem Multimethod.register_sound (generic updated : Multimethod Args Method Result)
    (specializers : List Specializer) (method : Method)
    (arity : specializers.length = generic.arity)
    (success : generic.register specializers method = .ok updated) : updated.CacheSound := by
  have empty := generic.register_cache_empty specializers method arity
  rw [success] at empty
  simp only [Except.map, Except.ok.injEq] at empty
  exact updated.cacheSound_of_empty empty

theorem Multimethod.contribute_sound (generic updated : Multimethod Args Method Result)
    (specializers : List Specializer) (method : Method)
    (arity : specializers.length = generic.arity)
    (success : generic.contribute specializers method = .ok updated) : updated.CacheSound := by
  have empty := generic.contribute_cache_empty specializers method arity
  rw [success] at empty
  simp only [Except.map, Except.ok.injEq] at empty
  exact updated.cacheSound_of_empty empty

theorem Multimethod.registerWhen_sound (generic updated : Multimethod Args Method Result)
    (specializers : List Specializer) (predicate : Args → Bool) (method : Method)
    (arity : specializers.length = generic.arity)
    (success : generic.registerWhen specializers predicate method = .ok updated) : updated.CacheSound := by
  have empty := generic.registerWhen_cache_empty specializers predicate method arity
  rw [success] at empty
  simp only [Except.map, Except.ok.injEq] at empty
  exact updated.cacheSound_of_empty empty

theorem Multimethod.candidates_reference (generic : Multimethod Args Method Result)
    (shape : DispatchShape) :
    (generic.candidatesFor shape).toList = generic.index.reference
      (shape.map fun order => order.map Specializer.prototype ++ [.any]) := by
  simpa [candidatesFor] using MethodIndex.collect_reference generic.index
    (shape.map fun order => order.map Specializer.prototype ++ [.any]) #[]

theorem Multimethod.resolve_correct (generic : Multimethod Args Method Result)
    (sound : generic.CacheSound) (args : Args)
    (arity : (generic.precedence args).length = generic.arity) :
    (generic.resolve args).map Prod.fst = .ok (generic.candidatesFor (generic.precedence args)) := by
  cases found : generic.cache.get? (generic.precedence args) with
  | none => simp [resolve, arity, found]; rfl
  | some methods =>
    have correct := sound _ _ found
    simp [resolve, arity, found, correct]
    rfl

theorem Multimethod.resolve_preserves (generic : Multimethod Args Method Result)
    (sound : generic.CacheSound) (args : Args) (methods : Array (MethodCandidate Args Method))
    (updated : Multimethod Args Method Result) (success : generic.resolve args = .ok (methods, updated)) :
    updated.CacheSound := by
  by_cases arity : (generic.precedence args).length = generic.arity
  · cases found : generic.cache.get? (generic.precedence args) with
    | none =>
      simp [resolve, arity, found] at success
      rcases success with ⟨rfl, rfl⟩
      exact ShapeCache.sound_remember _ _ sound _ _ rfl
    | some values =>
      simp [resolve, arity, found] at success
      rcases success with ⟨rfl, rfl⟩
      exact ShapeCache.sound_touch _ _ sound _
  · simp [resolve, arity, bind, Except.bind, throw, Except.error] at success

/-- The semantic call uses ordered tuple enumeration without a cache. -/
def Multimethod.referenceCall (generic : Multimethod Args Method Result) (args : Args) :
    Except MultimethodError Result :=
  let shape := generic.precedence args
  if shape.length != generic.arity then .error (.arity generic.arity shape.length)
  else .ok (generic.combine
    ((generic.index.reference (shape.map fun order => order.map Specializer.prototype ++ [.any])).filterMap
      (MethodCandidate.selected args)).toArray args)

theorem Multimethod.call_correct (generic : Multimethod Args Method Result)
    (sound : generic.CacheSound) (args : Args) :
    (generic.call args).map Prod.fst = generic.referenceCall args := by
  have methods : MethodCandidate.select (generic.candidatesFor (generic.precedence args)) args =
      ((generic.index.reference ((generic.precedence args).map fun order =>
        order.map Specializer.prototype ++ [.any])).filterMap (MethodCandidate.selected args)).toArray := by
    apply Array.toList_inj.mp
    rw [MethodCandidate.select_reference, generic.candidates_reference, List.toList_toArray]
  by_cases arity : (generic.precedence args).length = generic.arity
  · have correct := generic.resolve_correct sound args arity
    cases result : generic.resolve args with
    | error error => simp [result, Except.map] at correct
    | ok pair =>
      have equal : pair.1 = generic.candidatesFor (generic.precedence args) := by
        simpa only [result, Except.map, Except.ok.injEq] using correct
      simp [call, referenceCall, result, arity, bind, Except.bind, Functor.map, Except.map, pure, Except.pure, equal, methods]
  · simp [call, resolve, referenceCall, arity, bind, Except.bind, throw, throwThe, Except.map, pure, Except.pure]
    rfl

end LeanPoo.Object
