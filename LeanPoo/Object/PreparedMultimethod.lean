import LeanPoo.Object.Multimethod
import LeanPoo.Object.MultimethodSemantics

/-!
The paper's efficient-dispatch path caches effective methods as well as C4
candidate lookup. A prepared effective method is reusable only when every
candidate on the shape is unconditional. Guarded methods retain the candidate
cache but reselect and prepare on each call, since their applicability may
change without a C4 shape change.
-/

namespace LeanPoo.Object

/-- `prepare` constructs an effective method from ordered contributions;
`invoke` supplies the current arguments. The two caches have different
validity rules and are invalidated together on method registration. -/
structure PreparedMultimethod (Args Method Effective Result : Type) where
  generic : Multimethod Args Method Unit
  prepare : Array Method → Effective
  invoke : Effective → Args → Result
  effectiveCache : ShapeCache Effective := {}

namespace PreparedMultimethod

def create (arity : Nat) (precedence : Args → List (List String))
    (prepare : Array Method → Effective)
    (invoke : Effective → Args → Result) :
    PreparedMultimethod Args Method Effective Result :=
  { generic := { arity, precedence, combine := fun _ _ => () }
    prepare
    invoke }

def register (prepared : PreparedMultimethod Args Method Effective Result)
    (specializers : List Specializer) (method : Method) :
    Except MultimethodError
      (PreparedMultimethod Args Method Effective Result) := do
  let updated ← prepared.generic.register specializers method
  return { prepared with generic := updated, effectiveCache := {} }

/-- Keep earlier methods at one tuple and invalidate both dispatch caches. -/
def contribute (prepared : PreparedMultimethod Args Method Effective Result)
    (specializers : List Specializer) (method : Method) :
    Except MultimethodError
      (PreparedMultimethod Args Method Effective Result) := do
  let updated ← prepared.generic.contribute specializers method
  return { prepared with generic := updated, effectiveCache := {} }

def registerWhen (prepared : PreparedMultimethod Args Method Effective Result)
    (specializers : List Specializer) (predicate : Args → Bool)
    (method : Method) :
    Except MultimethodError
      (PreparedMultimethod Args Method Effective Result) := do
  let updated ← prepared.generic.registerWhen specializers predicate method
  return { prepared with generic := updated, effectiveCache := {} }

/-- A stable shape uses its precomputed effective method. A guarded shape
rechecks predicates and prepares only the applicable methods for this call. -/
def call (prepared : PreparedMultimethod Args Method Effective Result)
    (args : Args) : Except MultimethodError
      (Result × PreparedMultimethod Args Method Effective Result) := do
  let shape := prepared.generic.precedence args
  match prepared.effectiveCache.get? shape with
  | some effective =>
      return (prepared.invoke effective args,
        { prepared with effectiveCache := prepared.effectiveCache.touch shape })
  | none => pure ()
  let (candidates, updatedGeneric) ← prepared.generic.resolve args
  let updated := { prepared with generic := updatedGeneric }
  if candidates.all MethodCandidate.unconditional then
    let effective := prepared.prepare
      (MethodCandidate.select candidates args)
    return (prepared.invoke effective args,
      { updated with effectiveCache :=
          prepared.effectiveCache.remember shape effective })
  else
    let effective := prepared.prepare
      (MethodCandidate.select candidates args)
    return (prepared.invoke effective args, updated)

end PreparedMultimethod
end LeanPoo.Object

namespace LeanPoo.Object.Multimethod

/-- Resolution changes only the candidate cache, preserving the dispatch
signature, precedence callback and method definition used by effective caches. -/
theorem resolve_definition (generic updated : Multimethod A Method R) (args : A) (candidates)
    (resolved : generic.resolve args = .ok (candidates, updated)) :
    updated.arity = generic.arity ∧ updated.precedence = generic.precedence ∧ updated.index = generic.index := by
  by_cases arity : (generic.precedence args).length = generic.arity
  · cases found : generic.cache.get? (generic.precedence args) <;>
      simp [resolve, arity, found] at resolved <;> rcases resolved with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  · simp [resolve, arity, bind, Except.bind, throw, throwThe] at resolved

end LeanPoo.Object.Multimethod

namespace LeanPoo.Object.ShapeCache

/-- A shape/value invariant generalizes cache soundness to dependent admission
conditions, including arity and argument-independent effective-method meaning. -/
def Holds (valid : DispatchShape → Value → Prop) (cache : ShapeCache Value) : Prop :=
  ∀ shape value, cache.get? shape = some value → valid shape value

/-- Empty caches contain no unadmitted effective methods. -/
theorem holds_empty (valid : DispatchShape → Value → Prop) : Holds valid {} := by
  intro shape value found
  simp [get?] at found

/-- Inserting an admitted value and evicting bounded stale entries preserve all
remaining admissions; eviction cannot turn a guarded shape into a compiled hit. -/
theorem holds_remember (valid : DispatchShape → Value → Prop) (cache : ShapeCache Value)
    (sound : Holds valid cache) (shape : DispatchShape) (value : Value) (accepted : valid shape value) :
    Holds valid (cache.remember shape value) := by
  have inserted : ∀ query item, (cache.values.insert shape value)[query]? = some item → valid query item := by
    intro query item found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · rename_i same
      have equal : shape = query := by simpa using same
      cases equal
      exact (Option.some.inj found) ▸ accepted
    · exact sound query item found
  have preserve (stales : List DispatchShape) (table : Std.HashMap DispatchShape Value)
      (admitted : ∀ query item, table[query]? = some item → valid query item) :
      ∀ query item, (stales.foldl (fun current stale => current.erase stale) table)[query]? = some item → valid query item := by
    induction stales generalizing table with
    | nil => exact admitted
    | cons stale rest ih =>
      apply ih
      intro query item found
      rw [Std.HashMap.getElem?_erase] at found
      split at found
      · contradiction
      · exact admitted query item found
  exact preserve _ _ inserted

/-- Moving a hit to the front changes only recency, never its admission. -/
theorem holds_touch (valid : DispatchShape → Value → Prop) (cache : ShapeCache Value)
    (sound : Holds valid cache) (shape : DispatchShape) : Holds valid (cache.touch shape) := by
  unfold touch
  split
  · exact sound
  · cases found : cache.get? shape with
    | none => exact sound
    | some value => exact holds_remember valid cache sound shape value (sound shape value found)

end LeanPoo.Object.ShapeCache

namespace LeanPoo.Object.PreparedMultimethod

/-- Unconditional selection is argument independent. Presence of even one
value-sensitive guard prevents this justification for effective-method reuse. -/
theorem unconditional_select (candidates : Array (MethodCandidate A Method))
    (unconditional : candidates.all MethodCandidate.unconditional = true) (first second : A) :
    MethodCandidate.select candidates first = MethodCandidate.select candidates second := by
  apply Array.toList_inj.mp
  rw [MethodCandidate.select_reference, MethodCandidate.select_reference]
  have all : candidates.toList.all MethodCandidate.unconditional = true := by
    simpa only [Array.all_toList] using unconditional
  generalize candidates.toList = items at all ⊢
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp_all [MethodCandidate.unconditional, MethodCandidate.selected, MethodCandidate.applies]

/-- A declared unconditional shape can compile its method data without inventing
an Args value or evaluating a guard. Every later selection yields this same array. -/
theorem unconditional_select_map (candidates : Array (MethodCandidate A Method))
    (unconditional : candidates.all MethodCandidate.unconditional = true) (args : A) :
    MethodCandidate.select candidates args = candidates.map MethodCandidate.method := by
  apply Array.toList_inj.mp
  rw [MethodCandidate.select_reference, Array.toList_map]
  have all : candidates.toList.all MethodCandidate.unconditional = true := by
    simpa only [Array.all_toList] using unconditional
  generalize candidates.toList = items at all ⊢
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp_all [MethodCandidate.unconditional, MethodCandidate.selected,
      MethodCandidate.applies, MethodCandidate.method]

/-- Compile a declared C4 shape at construction, before admission probes discard
invocation successors. No argument, body, guard or invocation result is evaluated.
Only unconditional shapes are admitted; current calls retain their ordinary C4,
arity and guarded-selection semantics. Entries count against actual cache budgets. -/
def prepareShape (prepared : PreparedMultimethod A Method Effective R) (shape : DispatchShape) :
    Except MultimethodError (PreparedMultimethod A Method Effective R) := do
  if shape.length != prepared.generic.arity then throw (.arity prepared.generic.arity shape.length)
  match prepared.effectiveCache.get? shape with
  | some _ => return { prepared with
      generic := { prepared.generic with cache := prepared.generic.cache.touch shape }
      effectiveCache := prepared.effectiveCache.touch shape }
  | none =>
    let candidates := prepared.generic.candidatesFor shape
    if candidates.all MethodCandidate.unconditional then
      return { prepared with
        generic := { prepared.generic with cache := prepared.generic.cache.remember shape candidates }
        effectiveCache := prepared.effectiveCache.remember shape
          (prepared.prepare (candidates.map MethodCandidate.method)) }
    else return prepared

/-- Guarded declared shapes remain unchanged; in particular no guard is sampled
with made-up values to justify preparing an effective method. -/
theorem prepareShape_guarded (prepared : PreparedMultimethod A Method Effective R) (shape : DispatchShape)
    (arity : shape.length = prepared.generic.arity) (miss : prepared.effectiveCache.get? shape = none)
    (guarded : (prepared.generic.candidatesFor shape).all MethodCandidate.unconditional = false) :
    prepared.prepareShape shape = .ok prepared := by
  simp [prepareShape, arity, miss, guarded, pure, Except.pure]

/-- Construction-time shape declarations cannot bypass dispatch arity. -/
theorem prepareShape_arity (prepared : PreparedMultimethod A Method Effective R) (shape : DispatchShape)
    (invalid : shape.length ≠ prepared.generic.arity) :
    prepared.prepareShape shape = .error (.arity prepared.generic.arity shape.length) := by
  simp [prepareShape, invalid, throw, throwThe, bind, Except.bind]
  rfl

/-- The uncached mathematical control still reselects current arguments and
performs the same arity check as the sparse candidate resolver. -/
def referenceCall (prepared : PreparedMultimethod A Method Effective R) (args : A) :
    Except MultimethodError R :=
  let shape := prepared.generic.precedence args
  if shape.length != prepared.generic.arity then .error (.arity prepared.generic.arity shape.length)
  else .ok (prepared.invoke (prepared.prepare
    (MethodCandidate.select (prepared.generic.candidatesFor shape) args)) args)

/-- Cache admission includes arity and equality to current-definition preparation
for EVERY argument of the shape, rather than equality of a previous result. -/
def EffectiveSound (prepared : PreparedMultimethod A Method Effective R) : Prop :=
  ∀ shape effective, prepared.effectiveCache.get? shape = some effective →
    shape.length = prepared.generic.arity ∧
    ∀ args, prepared.generic.precedence args = shape →
      effective = prepared.prepare (MethodCandidate.select (prepared.generic.candidatesFor shape) args)

/-- Every prepared hit invokes its method with the current arguments. Candidate
resolution and compilation are absent from this branch. -/
theorem call_hit (prepared : PreparedMultimethod A Method Effective R) (args : A) (effective : Effective)
    (hit : prepared.effectiveCache.get? (prepared.generic.precedence args) = some effective) :
    prepared.call args = .ok (prepared.invoke effective args,
      { prepared with effectiveCache := prepared.effectiveCache.touch (prepared.generic.precedence args) }) := by
  simp [call, hit, pure, Except.pure]

/-- A guarded candidate sequence is always reselected and recompiled, even when
its C4 candidate lookup was warm. It contributes no effective-cache entry. -/
theorem call_guarded (prepared : PreparedMultimethod A Method Effective R) (args : A)
    (candidates : Array (MethodCandidate A Method)) (updated : Multimethod A Method Unit)
    (miss : prepared.effectiveCache.get? (prepared.generic.precedence args) = none)
    (resolved : prepared.generic.resolve args = .ok (candidates, updated))
    (guarded : candidates.all MethodCandidate.unconditional = false) :
    prepared.call args = .ok (prepared.invoke (prepared.prepare (MethodCandidate.select candidates args)) args,
      { prepared with generic := updated }) := by
  simp [call, miss, resolved, guarded, bind, Except.bind, pure, Except.pure]

/-- Under explicit candidate/effective cache invariants, every hit, cold miss,
guarded fallback and arity refusal agrees with the uncached current definition. -/
theorem call_correct (prepared : PreparedMultimethod A Method Effective R)
    (candidatesSound : prepared.generic.CacheSound) (effectiveSound : prepared.EffectiveSound) (args : A) :
    (prepared.call args).map Prod.fst = prepared.referenceCall args := by
  cases hit : prepared.effectiveCache.get? (prepared.generic.precedence args) with
  | some effective =>
    have valid := effectiveSound _ _ hit
    rw [call_hit prepared args effective hit]
    simp [referenceCall, valid.1, valid.2 args rfl, Except.map]
  | none =>
    by_cases arity : (prepared.generic.precedence args).length = prepared.generic.arity
    · have correct := prepared.generic.resolve_correct candidatesSound args arity
      cases resolved : prepared.generic.resolve args with
      | error error => simp [resolved, Except.map] at correct
      | ok pair =>
        have same : pair.1 = prepared.generic.candidatesFor (prepared.generic.precedence args) := by
          simpa [resolved, Except.map] using correct
        cases guarded : (prepared.generic.candidatesFor (prepared.generic.precedence args)).all MethodCandidate.unconditional <;>
          simp [call, hit, resolved, referenceCall, arity, same, guarded, bind, Except.bind, pure, Except.pure, Except.map]
    · simp [call, hit, Multimethod.resolve, referenceCall, arity, bind, Except.bind, Except.map, throw, throwThe, pure, Except.pure]
      rfl

/-- Explicit preparation preserves both cache invariants. Its newly compiled
entry agrees with every future argument of that shape, and never freezes a guard. -/
theorem prepareShape_preserves (prepared updated : PreparedMultimethod A Method Effective R)
    (candidatesSound : prepared.generic.CacheSound) (effectiveSound : prepared.EffectiveSound)
    (shape : DispatchShape) (success : prepared.prepareShape shape = .ok updated) :
    updated.generic.CacheSound ∧ updated.EffectiveSound := by
  by_cases arity : shape.length = prepared.generic.arity
  · cases hit : prepared.effectiveCache.get? shape with
    | some effective =>
      simp [prepareShape, arity, hit, pure, Except.pure] at success
      cases success
      exact ⟨ShapeCache.sound_touch _ _ candidatesSound _, ShapeCache.holds_touch _ _ effectiveSound _⟩
    | none =>
      cases unconditional : (prepared.generic.candidatesFor shape).all MethodCandidate.unconditional with
      | false =>
        simp [prepareShape, arity, hit, unconditional, pure, Except.pure] at success
        cases success
        exact ⟨candidatesSound, effectiveSound⟩
      | true =>
        simp [prepareShape, arity, hit, unconditional, pure, Except.pure] at success
        cases success
        refine ⟨ShapeCache.sound_remember _ _ candidatesSound _ _ rfl, ?_⟩
        apply ShapeCache.holds_remember
        · exact effectiveSound
        · refine ⟨arity, ?_⟩
          intro args _same
          exact congrArg prepared.prepare (unconditional_select_map _ unconditional args).symm
  · simp [prepareShape, arity, throw, throwThe, bind, Except.bind] at success

/-- Preparing a cache changes neither the method definition nor its uncached
reference semantics, including missing methods, prefix failure and side effects. -/
theorem prepareShape_reference (prepared updated : PreparedMultimethod A Method Effective R)
    (shape : DispatchShape) (success : prepared.prepareShape shape = .ok updated) (args : A) :
    updated.referenceCall args = prepared.referenceCall args := by
  by_cases arity : shape.length = prepared.generic.arity
  · cases hit : prepared.effectiveCache.get? shape with
    | some effective =>
      simp [prepareShape, arity, hit, pure, Except.pure] at success
      cases success
      rfl
    | none =>
      cases unconditional : (prepared.generic.candidatesFor shape).all MethodCandidate.unconditional <;>
        simp [prepareShape, arity, hit, unconditional, pure, Except.pure] at success <;> cases success <;> rfl
  · simp [prepareShape, arity, throw, throwThe, bind, Except.bind] at success

/-- Prepared construction retains the exact dispatch definition and invoker.
Only caches change, which is the premise for transporting completed negative
watches rather than running probes/guards a second time during preparation. -/
theorem prepareShape_definition (prepared updated : PreparedMultimethod A Method Effective R)
    (shape : DispatchShape) (success : prepared.prepareShape shape = .ok updated) :
    updated.generic.index = prepared.generic.index ∧ updated.generic.arity = prepared.generic.arity ∧
    updated.generic.precedence = prepared.generic.precedence ∧ updated.prepare = prepared.prepare ∧
    updated.invoke = prepared.invoke := by
  by_cases arity : shape.length = prepared.generic.arity
  · cases hit : prepared.effectiveCache.get? shape with
    | some effective =>
      simp [prepareShape, arity, hit, pure, Except.pure] at success
      cases success
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | none =>
      cases unconditional : (prepared.generic.candidatesFor shape).all MethodCandidate.unconditional <;>
        simp [prepareShape, arity, hit, unconditional, pure, Except.pure] at success <;>
        cases success <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [prepareShape, arity, throw, throwThe, bind, Except.bind] at success

/-- Preparing a frontmost admitted shape needs no new cache owner and no repeat
compilation. Native fused resolution/effective entries implement the same law. -/
theorem prepareShape_recent (prepared : PreparedMultimethod A Method Effective R)
    (shape : DispatchShape) (effective : Effective)
    (arity : shape.length = prepared.generic.arity) (hit : prepared.effectiveCache.get? shape = some effective)
    (candidateRecent : prepared.generic.cache.recent.head? = some shape)
    (effectiveRecent : prepared.effectiveCache.recent.head? = some shape) :
    prepared.prepareShape shape = .ok prepared := by
  simp [prepareShape, arity, hit, ShapeCache.touch, candidateRecent, effectiveRecent, pure, Except.pure]

/-- Actual current-argument invocation on a frontmost compiled shape returns its
existing owner. The method still executes; only reconstruction is absent. -/
theorem call_recent (prepared : PreparedMultimethod A Method Effective R) (args : A) (effective : Effective)
    (hit : prepared.effectiveCache.get? (prepared.generic.precedence args) = some effective)
    (recent : prepared.effectiveCache.recent.head? = some (prepared.generic.precedence args)) :
    prepared.call args = .ok (prepared.invoke effective args, prepared) := by
  rw [call_hit prepared args effective hit]
  simp [ShapeCache.touch, recent]

/-- All actual calls after construction-time preparation agree with the original
uncached definition. The prepared entry never substitutes for current arguments. -/
theorem prepareShape_call_correct (prepared updated : PreparedMultimethod A Method Effective R)
    (candidatesSound : prepared.generic.CacheSound) (effectiveSound : prepared.EffectiveSound)
    (shape : DispatchShape) (success : prepared.prepareShape shape = .ok updated) (args : A) :
    (updated.call args).map Prod.fst = prepared.referenceCall args := by
  have preserved := prepared.prepareShape_preserves updated candidatesSound effectiveSound shape success
  rw [updated.call_correct preserved.1 preserved.2, prepared.prepareShape_reference updated shape success]

/-- Admission-style probes retain results and discard cache successors. Every
probe still dispatches using current arguments; no result is memoized here. -/
def probes (prepared : PreparedMultimethod A Method Effective R) (arguments : List A) :
    Except MultimethodError (List R) :=
  arguments.mapM (fun args => (prepared.call args).map Prod.fst)

/-- A whole sequence of discarded-successor probes agrees with current-definition
invocation after explicit preparation. This preserves method actions as well as
results, so later monadic execution cannot omit a prefix/guard/body check. -/
theorem prepareShape_probes (prepared updated : PreparedMultimethod A Method Effective R)
    (candidatesSound : prepared.generic.CacheSound) (effectiveSound : prepared.EffectiveSound)
    (shape : DispatchShape) (success : prepared.prepareShape shape = .ok updated) (arguments : List A) :
    updated.probes arguments = arguments.mapM prepared.referenceCall := by
  have same : (fun args => (updated.call args).map Prod.fst) = prepared.referenceCall := by
    funext args
    exact prepared.prepareShape_call_correct updated candidatesSound effectiveSound shape success args
  unfold probes
  rw [same]

/-- Both cache invariants are preserved by actual successful calls. A cold
unconditional shape admits an effective method for every argument of that shape;
guarded calls admit none, and hits only touch already admitted entries. -/
theorem call_preserves (prepared updated : PreparedMultimethod A Method Effective R)
    (candidatesSound : prepared.generic.CacheSound) (effectiveSound : prepared.EffectiveSound)
    (args : A) (result : R) (success : prepared.call args = .ok (result, updated)) :
    updated.generic.CacheSound ∧ updated.EffectiveSound := by
  cases hit : prepared.effectiveCache.get? (prepared.generic.precedence args) with
  | some effective =>
    rw [call_hit prepared args effective hit] at success
    cases Except.ok.inj success
    exact ⟨candidatesSound, ShapeCache.holds_touch _ _ effectiveSound _⟩
  | none =>
    cases resolved : prepared.generic.resolve args with
    | error error => simp [call, hit, resolved, bind, Except.bind] at success
    | ok pair =>
      have definition := prepared.generic.resolve_definition pair.2 args pair.1 resolved
      have preserved := prepared.generic.resolve_preserves candidatesSound args pair.1 pair.2 resolved
      have arity : (prepared.generic.precedence args).length = prepared.generic.arity := by
        by_cases valid : (prepared.generic.precedence args).length = prepared.generic.arity
        · exact valid
        · simp [Multimethod.resolve, valid, bind, Except.bind, throw, throwThe] at resolved
      have selected : pair.1 = prepared.generic.candidatesFor (prepared.generic.precedence args) := by
        have correct := prepared.generic.resolve_correct candidatesSound args arity
        simpa [resolved, Except.map] using correct
      have equivalent (shape : DispatchShape) : pair.2.candidatesFor shape = prepared.generic.candidatesFor shape := by
        simp [Multimethod.candidatesFor, definition.2.2]
      cases unconditional : pair.1.all MethodCandidate.unconditional with
      | false =>
        simp [call, hit, resolved, unconditional, bind, Except.bind, pure, Except.pure] at success
        rcases success with ⟨rfl, rfl⟩
        refine ⟨preserved, ?_⟩
        intro shape effective cached
        have old := effectiveSound shape effective cached
        exact ⟨definition.1.trans old.1.symm |>.symm, fun current same => by
          rw [equivalent]
          exact old.2 current (definition.2.1 ▸ same)⟩
      | true =>
        simp [call, hit, resolved, unconditional, bind, Except.bind, pure, Except.pure] at success
        rcases success with ⟨rfl, rfl⟩
        refine ⟨preserved, ?_⟩
        apply ShapeCache.holds_remember
        · intro shape effective cached
          have old := effectiveSound shape effective cached
          refine ⟨old.1.trans definition.1.symm, ?_⟩
          intro current same
          rw [equivalent]
          exact old.2 current (definition.2.1 ▸ same)
        · refine ⟨arity.trans definition.1.symm, ?_⟩
          intro current _same
          rw [equivalent, ← selected]
          exact congrArg prepared.prepare (unconditional_select pair.1 unconditional args current)

/-- Fresh prepared generics start with both cache invariants, for every pure
preparer/invoker. No agreement with a native compiler is assumed or concluded. -/
theorem create_sound (arity : Nat) (precedence : A → DispatchShape)
    (prepare : Array Method → Effective) (invoke : Effective → A → R) :
    (create arity precedence prepare invoke).generic.CacheSound ∧
      (create arity precedence prepare invoke).EffectiveSound := by
  exact ⟨ShapeCache.sound_empty _, ShapeCache.holds_empty _⟩

/-- Registration discards all effective entries, independently of the old cache. -/
theorem register_effective_empty (prepared updated : PreparedMultimethod A Method Effective R)
    (path : List Specializer) (method : Method) (generic : Multimethod A Method Unit)
    (registered : prepared.generic.register path method = .ok generic)
    (success : prepared.register path method = .ok updated) : updated.effectiveCache = {} := by
  simp [register, registered, bind, Except.bind, pure, Except.pure] at success
  cases success
  rfl

/-- Replacing one tuple starts with empty candidate/effective caches,
so no old guarded assumption or compiled method survives the definition edit. -/
theorem register_preserves (prepared updated : PreparedMultimethod A Method Effective R)
    (path : List Specializer) (method : Method) (arity : path.length = prepared.generic.arity)
    (success : prepared.register path method = .ok updated) :
    updated.generic.CacheSound ∧ updated.EffectiveSound := by
  cases registered : prepared.generic.register path method with
  | error error => simp [register, registered, bind, Except.bind] at success
  | ok generic =>
    simp [register, registered, bind, Except.bind, pure, Except.pure] at success
    cases success
    exact ⟨prepared.generic.register_sound generic path method arity registered, ShapeCache.holds_empty _⟩

/-- Adding an unconditional contribution starts with empty candidate/effective caches,
so no old guarded assumption or compiled method survives the definition edit. -/
theorem contribute_preserves (prepared updated : PreparedMultimethod A Method Effective R)
    (path : List Specializer) (method : Method) (arity : path.length = prepared.generic.arity)
    (success : prepared.contribute path method = .ok updated) :
    updated.generic.CacheSound ∧ updated.EffectiveSound := by
  cases registered : prepared.generic.contribute path method with
  | error error => simp [contribute, registered, bind, Except.bind] at success
  | ok generic =>
    simp [contribute, registered, bind, Except.bind, pure, Except.pure] at success
    cases success
    exact ⟨prepared.generic.contribute_sound generic path method arity registered, ShapeCache.holds_empty _⟩

/-- Adding a value-sensitive guard starts with empty candidate/effective caches,
so no old guarded assumption or compiled method survives the definition edit. -/
theorem registerWhen_preserves (prepared updated : PreparedMultimethod A Method Effective R)
    (path : List Specializer)
    (predicate : A → Bool) (method : Method) (arity : path.length = prepared.generic.arity)
    (success : prepared.registerWhen path predicate method = .ok updated) :
    updated.generic.CacheSound ∧ updated.EffectiveSound := by
  cases registered : prepared.generic.registerWhen path predicate method with
  | error error => simp [registerWhen, registered, bind, Except.bind] at success
  | ok generic =>
    simp [registerWhen, registered, bind, Except.bind, pure, Except.pure] at success
    cases success
    exact ⟨prepared.generic.registerWhen_sound generic path predicate method arity registered, ShapeCache.holds_empty _⟩

end LeanPoo.Object.PreparedMultimethod

namespace LeanPoo.Object

/-- Explicit nested-cache owner. The prepared outer effective method produces a
child-state computation; its child can itself be a nested owner. No mutable body
cell or cached result is required. The native invoker additionally checks child
index/invoker identity before transporting a negative-watch certificate. -/
structure NestedMultimethod (A Method Effective Child Error R : Type) where
  outer : PreparedMultimethod A Method Effective (Child → Except Error (R × Child))
  child : Child

namespace NestedMultimethod

/-- Dispatch first, run the selected child computation, then publish BOTH cache
successors together. Either failure returns no tentative owner. External effects
already performed by bodies are outside this immutable publication guarantee. -/
def call (owner : NestedMultimethod A Method Effective Child Error R) (args : A) :
    Except (MultimethodError ⊕ Error) (R × NestedMultimethod A Method Effective Child Error R) := do
  let (invoke, outer) ← (owner.outer.call args).mapError Sum.inl
  let (result, child) ← (invoke owner.child).mapError Sum.inr
  return (result, { outer, child })

/-- Successful child invocation transports its EXACT successor together with the
outer prepared cache. Repeated nesting composes by choosing Child as another owner. -/
theorem call_success (owner : NestedMultimethod A Method Effective Child Error R) (args : A)
    (invoke : Child → Except Error (R × Child)) (outer) (result : R) (child : Child)
    (dispatched : owner.outer.call args = .ok (invoke, outer))
    (invoked : invoke owner.child = .ok (result, child)) :
    owner.call args = .ok (result, { outer, child }) := by
  simp [call, dispatched, invoked, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A child refusal exposes no partially warmed outer owner to the publisher. -/
theorem call_child_failure (owner : NestedMultimethod A Method Effective Child Error R) (args : A)
    (invoke : Child → Except Error (R × Child)) (outer) (error : Error)
    (dispatched : owner.outer.call args = .ok (invoke, outer))
    (invoked : invoke owner.child = .error error) : owner.call args = .error (.inr error) := by
  simp [call, dispatched, invoked, Except.mapError, bind, Except.bind]

/-- Reusing a child cache cannot suppress outer dispatch refusal. -/
theorem call_dispatch_failure (owner : NestedMultimethod A Method Effective Child Error R) (args : A)
    (error : MultimethodError) (refused : owner.outer.call args = .error error) :
    owner.call args = .error (.inl error) := by
  simp [call, refused, Except.mapError, bind, Except.bind]

/-- A prepared outer hit and unchanged child successor retain the complete
nested owner, while still executing the current selected child computation.
This removes temporary owner construction in discarded admission probes. -/
theorem call_retains (owner : NestedMultimethod A Method Effective Child Error R) (args : A)
    (invoke : Child → Except Error (R × Child)) (result : R)
    (dispatched : owner.outer.call args = .ok (invoke, owner.outer))
    (invoked : invoke owner.child = .ok (result, owner.child)) :
    owner.call args = .ok (result, owner) := by
  rw [call_success owner args invoke owner.outer result owner.child dispatched invoked]

/-- Optional concrete child-provenance admission, corresponding to the native
index/invoker identity check. Its correctness as a definition test is a caller
premise; arbitrary higher-order function equality is not decidable in Lean. -/
def callChecked (owner : NestedMultimethod A Method Effective Child Error R) (args : A)
    (compatible : Child → Child → Bool) :
    Except ((MultimethodError ⊕ Error) ⊕ Unit) (R × NestedMultimethod A Method Effective Child Error R) := do
  let (result, next) ← (owner.call args).mapError Sum.inl
  if compatible owner.child next.child then return (result, next) else .error (.inr ())

/-- A checked successor satisfies the concrete child-provenance guard. This
prevents a method edit from being transported as if it were only cache state. -/
theorem callChecked_admitted (owner next : NestedMultimethod A Method Effective Child Error R)
    (args : A) (compatible : Child → Child → Bool) (result : R)
    (success : owner.callChecked args compatible = .ok (result, next)) :
    compatible owner.child next.child = true := by
  cases invoked : owner.call args with
  | error error => simp [callChecked, invoked, Except.mapError, bind, Except.bind] at success
  | ok pair =>
    cases valid : compatible owner.child pair.2.child <;>
      simp [callChecked, invoked, valid, Except.mapError, bind, Except.bind, pure, Except.pure] at success
    rcases success with ⟨rfl, rfl⟩
    exact valid

/-- A changed child definition/invoker cannot expose either tentative cache owner. -/
theorem callChecked_refused (owner next : NestedMultimethod A Method Effective Child Error R)
    (args : A) (compatible : Child → Child → Bool) (result : R)
    (invoked : owner.call args = .ok (result, next)) (invalid : compatible owner.child next.child = false) :
    owner.callChecked args compatible = .error (.inr ()) := by
  simp [callChecked, invoked, invalid, Except.mapError, bind, Except.bind]

end NestedMultimethod
end LeanPoo.Object

namespace LeanPoo.Object
/-- Prepared code computes a context-parameterized result. Context is invocation
DATA, never an input to candidate selection, guards or effective preparation. -/
structure PreparedContextMultimethod (A Method Effective Context R : Type) where
  program : PreparedMultimethod A Method Effective (Context → R)
  context : Context
namespace PreparedContextMultimethod
/-- A typed context update preserves the entire prepared definition and caches. -/
def bindContext (owner : PreparedContextMultimethod A Method Effective C R) (context : C) :=
  { owner with context }
/-- Applicability and effective code are identical, so their negative/positive
properties need no new construction or retagging after a typed data binding. -/
theorem bindContext_program (owner : PreparedContextMultimethod A Method Effective C R) (context : C) :
    (owner.bindContext context).program = owner.program := rfl
/-- All arguments still pass through the existing sparse prepared dispatcher. -/
def call (owner : PreparedContextMultimethod A Method Effective C R) (args : A) :
    Except MultimethodError (R × PreparedContextMultimethod A Method Effective C R) := do
  let (invoke, program) ← owner.program.call args
  return (invoke owner.context, { owner with program })
/-- Warm code never memoizes an invocation result; it evaluates the current
argument against the owner's newly bound context on EVERY call. -/
theorem call_correct (owner : PreparedContextMultimethod A Method Effective C R)
    (candidates : owner.program.generic.CacheSound) (effective : owner.program.EffectiveSound) (args : A) :
    (owner.call args).map Prod.fst =
      (owner.program.referenceCall args).map (fun invoke => invoke owner.context) := by
  rw [← owner.program.call_correct candidates effective args]
  cases dispatched : owner.program.call args <;>
    simp [call, dispatched, Except.map, bind, Except.bind, pure, Except.pure]
/-- Rebinding retains both cache invariants because neither cached code nor its
argument-only guards depend on the data stored in this owner. -/
theorem bindContext_sound (owner : PreparedContextMultimethod A Method Effective C R)
    (context : C) (candidates : owner.program.generic.CacheSound) (effective : owner.program.EffectiveSound) :
    (owner.bindContext context).program.generic.CacheSound ∧ (owner.bindContext context).program.EffectiveSound :=
  ⟨candidates, effective⟩
/-- A real warm call executes its computation while retaining the exact owner. -/
theorem call_retains (owner : PreparedContextMultimethod A Method Effective C R)
    (args : A) (invoke : C → R) (hit : owner.program.call args = .ok (invoke, owner.program)) :
    owner.call args = .ok (invoke owner.context, owner) := by
  simp [call, hit, bind, Except.bind, pure, Except.pure]

/-- Cache evolution changes neither the bound context nor its typed owner data. -/
theorem call_context (owner next : PreparedContextMultimethod A Method Effective C R)
    (args : A) (result : R) (success : owner.call args = .ok (result, next)) : next.context = owner.context := by
  cases dispatched : owner.program.call args with
  | error error => simp [call, dispatched, bind, Except.bind] at success
  | ok pair =>
    simp [call, dispatched, bind, Except.bind, pure, Except.pure] at success
    rcases success with ⟨rfl, rfl⟩
    rfl
end PreparedContextMultimethod

/-- A nested cache transport cannot smuggle a context change into a business
call. Data changes require the separate checked reconstruction/publication path. -/
theorem NestedMultimethod.callChecked_context_change [DecidableEq C]
    (owner next : NestedMultimethod A Method Effective (PreparedContextMultimethod B BM BE C S) Error R)
    (args : A) (result : R) (invoked : owner.call args = .ok (result, next))
    (changed : owner.child.context ≠ next.child.context) :
    owner.callChecked args (fun before after => decide (before.context = after.context)) = .error (.inr ()) := by
  apply owner.callChecked_refused next args _ result invoked
  simp [changed]
end LeanPoo.Object
