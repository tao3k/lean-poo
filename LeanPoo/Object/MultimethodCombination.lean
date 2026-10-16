import LeanPoo.Object.MethodCombinationSemantics
import LeanPoo.Object.Multimethod
import LeanPoo.Object.MultimethodSemantics
import LeanPoo.Object.MethodCombination
import LeanPoo.Object.PreparedMultimethod
import LeanPoo.Object.QualifiedMethods

/-!
The paper separates multiple dispatch into an accepter, a combiner, and an
invoker. `Multimethod` owns the C4 accepter and sparse method index. These
constructors use Lean's typed method-combination functions as combiners;
the complete `Args` value is passed to each method as the invoker's record.
-/

namespace LeanPoo.Object.Multimethod

/-- User-defined method combination. C4 and the sparse tuple index select
contributions; the interpreter receives them grouped by their dependent
qualifiers in precedence order. No new dispatch or slot evaluator is needed. -/
def qualified {Args Result : Type} {Qualifier : Type}
    {Body : Qualifier → Type} [DecidableEq Qualifier]
    (arity : Nat) (precedence : Args → List (List String))
    (interpret : QualifiedMethods Qualifier Body → Args → Result) :
    Multimethod Args (Sigma Body) Result :=
  { arity
    precedence
    combine := fun contributions args =>
      interpret (QualifiedMethods.prependAll contributions.toList {}) args }

/-- Combine qualified multimethod contributions in lexicographic C4 order.
The result of dispatch is a standard effective method, with around, before,
primary, and after groups. -/
def standard {Args : Type} {M : Type → Type} {Result : Type} [Monad M]
    (arity : Nat) (precedence : Args → List (List String))
    (onMissing : Args → M Result) :
    Multimethod Args
      (MethodCombination.Contribution Args M Result) (M Result) :=
  { arity
    precedence
    combine := fun contributions args =>
      let methods := contributions.toList.foldr
        (fun contribution methods => methods.prepend contribution)
        ({} : MethodCombination.Methods Args M Result)
      (MethodCombination.effective methods onMissing) args }

/-- A simple multimethod combines item results with the given policy. Around
methods retain the ordinary next-method chain around that computation. -/
def simple {Args : Type} {M : Type → Type}
    {Item Acc Result : Type} [Monad M]
    (arity : Nat) (precedence : Args → List (List String))
    (policy : MethodCombination.SimplePolicy Item Acc Result) :
    Multimethod Args
      (MethodCombination.SimpleContribution Args M Item Result) (M Result) :=
  { arity
    precedence
    combine := fun contributions args =>
      let methods := contributions.toList.foldr
        (fun contribution methods => methods.prepend contribution)
        ({} : MethodCombination.SimpleMethods Args M Item Result)
      (MethodCombination.simpleEffective policy methods) args }

/-- A typed calling convention for a fixed dispatch tuple and a forwardable
payload. Methods can update the payload passed to `next`, while Lean's product
type prevents them from replacing the already-dispatched C4 arguments. -/
def forwardingStandard {Dispatch Payload : Type} {M : Type → Type}
    {Result : Type} [Monad M]
    (arity : Nat) (precedence : Dispatch → List (List String))
    (onMissing : (Dispatch × Payload) → M Result) :
    Multimethod (Dispatch × Payload)
      (MethodCombination.ForwardContribution Dispatch Payload M Result)
      (M Result) :=
  { arity
    precedence := fun call => precedence call.1
    combine := fun contributions call =>
      let methods := contributions.toList.foldr
        (fun contribution methods => methods.prepend contribution)
        ({} : MethodCombination.ForwardMethods Dispatch Payload M Result)
      (MethodCombination.forwardEffective methods onMissing) call }

/-- BETA-style superclass-controlled `inner` over the C4-selected methods. -/
def inner {Args : Type} {M : Type → Type} {Result : Type}
    (arity : Nat) (precedence : Args → List (List String))
    (onInnermost : Args → M Result) :
    Multimethod Args (MethodCombination.SubMethod Args M Result) (M Result) :=
  { arity
    precedence
    combine := fun methods args =>
      (MethodCombination.innerChain methods.toList onInnermost) args }

/-- Simula-style automatic `inner` for prefix/suffix class bodies. -/
def simula {Args : Type} {M : Type → Type} [Monad M]
    (arity : Nat) (precedence : Args → List (List String)) :
    Multimethod Args (MethodCombination.SimulaBody Args M) (M Unit) :=
  { arity
    precedence
    combine := fun methods args =>
      (MethodCombination.simulaEffective methods.toList) args }

/-- Precompute the standard effective method once per unconditional C4
shape. Shapes containing guarded contributions still use per-call selection. -/
def preparedStandard {Args : Type} {M : Type → Type} {Result : Type}
    [Monad M] (arity : Nat)
    (precedence : Args → List (List String))
    (onMissing : Args → M Result) :
    PreparedMultimethod Args
      (MethodCombination.Contribution Args M Result)
      (Args → M Result) (M Result) :=
  PreparedMultimethod.create arity precedence
    (fun contributions =>
      let methods := contributions.toList.foldr
        (fun contribution methods => methods.prepend contribution)
        ({} : MethodCombination.Methods Args M Result)
      MethodCombination.effective methods onMissing)
    (fun effective args => effective args)

end LeanPoo.Object.Multimethod

/-! Operational laws for forwarding and superclass-controlled combinations.
These refine the original reference's open combination direction; forwarding
payloads and inner/Simula are explicit extensions, not verbatim Racket code. -/
namespace LeanPoo.Object.MethodCombination

/-- Recursive reference evaluator exposes the fixed dispatch value in each
continuation. Optional replacements change only the typed payload component. -/
def forwardReference {D P : Type} {M : Type → Type} {R : Type}
    (methods : List (ForwardMethod D P M R)) (terminal : (D × P) → M R) : (D × P) → M R :=
  match methods with
  | [] => terminal
  | method :: rest => fun call => method
      (fun replacement => forwardReference rest terminal (call.1, replacement.getD call.2)) call

/-- The executable fold preserves the recursive protocol for arbitrary methods,
including methods omitting or invoking the continuation multiple times. -/
theorem callForwardChain_reference {D P : Type} {M : Type → Type} {R : Type}
    (methods : List (ForwardMethod D P M R)) (terminal : (D × P) → M R) :
    callForwardChain methods terminal = forwardReference methods terminal := by
  induction methods with
  | nil => rfl
  | cons method rest ih => simp [callForwardChain, forwardReference, ← ih]

/-- Separately defined forwarding fragments compose without another dispatch
lookup. Both layers retain the same fixed dispatch argument. -/
theorem callForwardChain_append {D P : Type} {M : Type → Type} {R : Type}
    (outer inner : List (ForwardMethod D P M R)) (terminal : (D × P) → M R) :
    callForwardChain (outer ++ inner) terminal = callForwardChain outer (callForwardChain inner terminal) := by
  simp [callForwardChain, List.foldr_append]

/-- A method declining next prevents every suffix body and the terminal from
executing. This law requires no purity or lawfulness assumption on M. -/
theorem callForwardChain_stop {D P : Type} {M : Type → Type} {R : Type}
    (stop : (D × P) → M R) (rest : List (ForwardMethod D P M R)) (terminal) :
    callForwardChain ((fun _ call => stop call) :: rest) terminal = stop := rfl

/-- C4 supplies specific-first groups; superclass control runs the reversed
inherited group around the reversed specialized group with original arguments. -/
theorem innerChain_append {A : Type} {M : Type → Type} {R : Type}
    (specific general : List (SubMethod A M R)) (terminal : A → M R) :
    innerChain (specific ++ general) terminal = callChain general.reverse (innerChain specific terminal) := by
  simp only [innerChain, List.reverse_append, callChain_append]

/-- An inherited body omitting inner blocks all descendants, independently of
what their bodies or innermost default would have done. -/
theorem innerChain_stop {A : Type} {M : Type → Type} {R : Type}
    (specific : List (SubMethod A M R)) (stop : A → M R) (terminal) :
    innerChain (specific ++ [fun _ args => stop args]) terminal = stop := by
  simp [innerChain, List.reverse_append, callChain]

/-- General-first prefixes followed by specific-first suffixes, for arbitrary
lawful monadic effects. An unsuccessful prefix has no subsequent suffix step. -/
theorem simulaEffective_pair {A : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (specific general : SimulaBody A M) (args : A) :
    simulaEffective [specific,general] args = (do
      general.prefixPart args; specific.prefixPart args
      specific.suffixPart args; general.suffixPart args) := by
  simp [simulaEffective]

/-- Failure preserves the state reached by executed prefixes and does not run
any suffix. Publication must separately decide which snapshot may be exposed. -/
theorem simulaEffective_prefix_failure {A State Error : Type}
    (specific general : SimulaBody A (EStateM Error State)) (args : A)
    (old reached failed : State) (error : Error)
    (first : general.prefixPart args old = .ok () reached)
    (second : specific.prefixPart args reached = .error error failed) :
    simulaEffective [specific,general] args old = .error error failed := by
  rw [simulaEffective_pair]
  simp [bind, EStateM.bind, first, second]

/-- Compile ordered side callbacks once; the continuation receives current arguments. -/
def compileParts {A B : Type} {M : Type → Type} [Monad M]
    (part : B → A → M Unit) (methods : List B) (terminal : A → M Unit) : A → M Unit :=
  methods.foldr (fun body next args => do part body args; next args) terminal
/-- Compilation preserves sequencing for arbitrary lawful effects and a suffix. -/
theorem compileParts_correct {A B : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (part : B → A → M Unit) (methods : List B) (terminal : A → M Unit) (args : A) :
    compileParts part methods terminal args = (do
      for body in methods do part body args
      terminal args) := by
  induction methods with
  | nil => simp [compileParts]
  | cons body rest ih => simp_all [compileParts]
/-- Build general-first prefix and specific-first suffix closures at preparation. -/
def compileSimula {A : Type} {M : Type → Type} [Monad M]
    (methods : List (SimulaBody A M)) : A → M Unit :=
  let suffix := compileParts SimulaBody.suffixPart methods (fun _ => pure ())
  methods.foldl (fun next body args => do body.prefixPart args; next args) suffix
/-- Both folds preserve the original Simula effect/failure order on every call. -/
theorem compileSimula_correct {A : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (methods : List (SimulaBody A M)) (args : A) :
    compileSimula methods args = simulaEffective methods args := by
  unfold compileSimula
  rw [List.foldl_eq_foldr_reverse]
  change compileParts SimulaBody.prefixPart methods.reverse
    (compileParts SimulaBody.suffixPart methods (fun _ => pure ())) args = _
  rw [compileParts_correct, compileParts_correct]
  simp [simulaEffective]

end LeanPoo.Object.MethodCombination

/-! Prepared invokers and explicit nested state advance the generalized protocol's
future-work direction. A cached value is an effective method, never its result. -/
namespace LeanPoo.Object.Multimethod

/-- Prepare forwarding groups once while retaining the fixed dispatch and typed
payload argument at invocation. Guarded shapes use the existing guarded fallback. -/
def preparedForwardingStandard {D P : Type} {M : Type → Type} {R : Type} [Monad M]
    (arity : Nat) (precedence : D → DispatchShape) (missing : (D × P) → M R) :
    PreparedMultimethod (D × P) (MethodCombination.ForwardContribution D P M R)
      ((D × P) → M R) (M R) :=
  PreparedMultimethod.create arity (fun args => precedence args.1)
    (fun contributions => MethodCombination.forwardEffective
      (contributions.toList.foldr (fun item methods => methods.prepend item) {}) missing)
    (fun effective args => effective args)

/-- Specialize simple-policy groups without executing item or around bodies. -/
def preparedSimple {A : Type} {M : Type → Type} {Item Acc R : Type} [Monad M]
    (arity : Nat) (precedence : A → DispatchShape)
    (policy : MethodCombination.SimplePolicy Item Acc R) :
    PreparedMultimethod A (MethodCombination.SimpleContribution A M Item R) (A → M R) (M R) :=
  PreparedMultimethod.create arity precedence
    (fun contributions => MethodCombination.simpleEffective policy
      (contributions.toList.foldr (fun item methods => methods.prepend item) {}))
    (fun effective args => effective args)

/-- Precompute the superclass-first continuation skeleton for inner control. -/
def preparedInner {A : Type} {M : Type → Type} {R : Type}
    (arity : Nat) (precedence : A → DispatchShape) (terminal : A → M R) :
    PreparedMultimethod A (MethodCombination.SubMethod A M R) (A → M R) (M R) :=
  PreparedMultimethod.create arity precedence
    (fun methods => MethodCombination.innerChain methods.toList terminal) (fun effective args => effective args)

/-- Precompute the Simula combination for each unconditional shape. -/
def preparedSimula {A : Type} {M : Type → Type} [Monad M]
    (arity : Nat) (precedence : A → DispatchShape) :
    PreparedMultimethod A (MethodCombination.SimulaBody A M) (A → M Unit) (M Unit) :=
  PreparedMultimethod.create arity precedence
    (fun methods => MethodCombination.simulaEffective methods.toList) (fun effective args => effective args)

/-- Preparation of forwarding contributions preserves the existing combination,
including payload replacement and all monadic failure/effect sequencing laws. -/
theorem preparedForwardingStandard_eq {D P : Type} {M : Type → Type} {R : Type} [Monad M]
    (arity : Nat) (precedence : D → DispatchShape) (missing : (D × P) → M R)
    (methods : Array (MethodCombination.ForwardContribution D P M R)) (args : D × P) :
    (preparedForwardingStandard arity precedence missing).prepare methods args =
      (forwardingStandard arity precedence missing).combine methods args := rfl

/-- Simple-policy precompilation preserves exact stop/empty/finalization semantics. -/
theorem preparedSimple_eq {A : Type} {M : Type → Type} {Item Acc R : Type} [Monad M]
    (arity : Nat) (precedence : A → DispatchShape) (policy : MethodCombination.SimplePolicy Item Acc R)
    (methods : Array (MethodCombination.SimpleContribution A M Item R)) (args : A) :
    (preparedSimple arity precedence policy).prepare methods args =
      (simple arity precedence policy).combine methods args := rfl

/-- Preparing the inner chain retains omission and repeated-next behavior. -/
theorem preparedInner_eq {A : Type} {M : Type → Type} {R : Type}
    (arity : Nat) (precedence : A → DispatchShape) (terminal : A → M R)
    (methods : Array (MethodCombination.SubMethod A M R)) (args : A) :
    (preparedInner arity precedence terminal).prepare methods args =
      (inner arity precedence terminal).combine methods args := rfl

/-- Preparing Simula preserves the general-first prefix/specific-first suffix
semantics. The native implementation independently extracts callbacks once. -/
theorem preparedSimula_eq {A : Type} {M : Type → Type} [Monad M]
    (arity : Nat) (precedence : A → DispatchShape)
    (methods : Array (MethodCombination.SimulaBody A M)) (args : A) :
    (preparedSimula arity precedence).prepare methods args =
      (simula arity precedence).combine methods args := rfl

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
