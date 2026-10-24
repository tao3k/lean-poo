import LeanPoo.Prototype.PreparedHooks
import LeanPoo.Object.Instantiation
import LeanPoo.Functional.RecursiveHandling
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

/-- Binding the immutable context during construction commutes with callback
compilation. Every call still supplies its own current unbound argument. -/
theorem compileParts_contramap {A B C : Type} {M : Type → Type} [Monad M]
    (part : B → A → M Unit) (methods : List B) (terminal : A → M Unit)
    (input : C → A) (args : C) :
    compileParts (fun body current => part body (input current)) methods
      (fun current => terminal (input current)) args = compileParts part methods terminal (input args) := by
  induction methods with
  | nil => rfl
  | cons body rest ih => simp_all [compileParts]
/-- Specialize fixed context without allocating another argument representation
at invocation. Native code directly calls the two-argument prefix/suffix callbacks. -/
def bindSimula {A C : Type} {M : Type → Type} [Monad M]
    (methods : List (SimulaBody (A × C) M)) (context : C) : A → M Unit :=
  let suffix := compileParts (fun body args => body.suffixPart (args, context)) methods (fun _ => pure ())
  methods.foldl (fun next body args => do body.prefixPart (args, context); next args) suffix
/-- For arbitrary lawful effects, context specialization retains every callback,
argument and failure position. No successful result or previous argument is reused. -/
theorem bindSimula_correct {A C : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (methods : List (SimulaBody (A × C) M)) (context : C) (args : A) :
    bindSimula methods context args = simulaEffective methods (args, context) := by
  unfold bindSimula
  rw [List.foldl_eq_foldr_reverse]
  have suffix : compileParts (fun (body : SimulaBody (A × C) M) current => body.suffixPart (current, context))
      methods (fun _ => pure ()) =
      (fun current => compileParts SimulaBody.suffixPart methods (fun _ => pure ()) (current, context)) := by
    funext current
    exact compileParts_contramap SimulaBody.suffixPart methods (fun _ => pure ()) (fun current => (current, context)) current
  rw [suffix]
  change compileParts (fun body current => body.prefixPart (current, context)) methods.reverse
    (fun current => compileParts SimulaBody.suffixPart methods (fun _ => pure ()) (current, context)) args = _
  rw [compileParts_contramap, compileParts_correct, compileParts_correct]
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







/-! Recursive evaluation companion for retained-state method workflows. These
laws reuse the existing evaluator; native receipts carry provenance, not proofs. -/
namespace LeanPoo.Prototype.Recursive.Cached
/-- A positive-budget warm request returns its exact receipt, entries and source
work counters; only the hit count changes. No body or continuation is re-evaluated. -/
theorem runCertified_hit [DecidableEq Input] (program : Generator Input Output)
    (cache : Cache program) (input : Input) (receipt : Receipt program (program input))
    (found : cache.lookup input = some receipt) (budget : Nat) :
    runCertified program input (budget + 1) cache = .ok (receipt,
      {cache with statistics := {cache.statistics with hits := cache.statistics.hits + 1}}) := by
  have executed : run program input (budget + 1) cache = .ok (receipt,
      {cache with statistics := {cache.statistics with hits := cache.statistics.hits + 1}}) := by
    simp only [run, resolve]
    rw [found]
  unfold runCertified
  split <;> simp_all
/-- Budget zero remains a diagnostic even when the root request is already warm. -/
theorem runCertified_zero [DecidableEq Input] (program : Generator Input Output)
    (cache : Cache program) (input : Input) :
    runCertified program input 0 cache = .error .budgetExhausted := rfl
end LeanPoo.Prototype.Recursive.Cached

namespace LeanPoo.Functional.RecursiveSession
open Prototype Prototype.Recursive Prototype.CallableRecord Object.Callable
/-- Raw memo reuse never reuses descriptor admission. The current registry's
fromReceipt checks run even on a one-step warm request; completed memo survives
an output refusal while input refusal remains handled before this theorem. -/
theorem call_warm_current (session : RecursiveSession program) (registry : Dynamic.Registry)
    (signature : Signature) (argument : Dynamic.Value) (budget fuel : Nat)
    (admitted : Dynamic.Admitted registry signature.input)
    (valid : signature.argumentType.validate registry fuel argument = .ok admitted)
    (receipt : Cached.Receipt program (program ⟨signature.name, argument⟩))
    (found : session.memo.lookup ⟨signature.name, argument⟩ = some receipt) :
    session.call registry signature argument (budget + 1) fuel =
      ⟨(CheckedCall.fromReceipt registry signature argument fuel
          ((signature.argumentType.validate_value registry fuel argument admitted valid) ▸ admitted.valid)
          receipt).mapError RecursiveFailure.boundary,
        ⟨{session.memo with statistics := {session.memo.statistics with hits := session.memo.statistics.hits + 1}}⟩,
        some true⟩ := by
  have completed := call_completed session registry signature argument (budget + 1) fuel admitted valid
    receipt _ (Cached.runCertified_hit program session.memo _ receipt found budget)
  simpa [found] using completed
end LeanPoo.Functional.RecursiveSession

namespace LeanPoo.Object.MethodCombination
variable {Item Acc Result Receiver : Type}
/-- Resolve a statically homogeneous item family through the original qualifier
constructor. General/mixed contributions must still retain their qualifiers. -/
def SimpleMethods.ofItems (items : List (Receiver → M Item)) : SimpleMethods Receiver M Item Result :=
  (items.map SimpleContribution.item).foldr (fun contribution methods => methods.prepend contribution) {}
/-- A known item-only family needs no qualifier objects or grouping pass. This
is a typed representation law, independent of effects performed by the bodies. -/
theorem SimpleMethods.ofItems_eq (items : List (Receiver → M Item)) :
    (SimpleMethods.ofItems items : SimpleMethods Receiver M Item Result) = { items := items } := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    change SimpleMethods.prepend (SimpleMethods.ofItems rest) (.item first) = _
    rw [ih]
    rfl
/-- Removing redundant item qualifiers preserves around-free simple combination
for every monad, including the first error and unexecuted short-circuit suffix. -/
theorem simpleEffective_ofItems {M : Type → Type} [Monad M]
    (policy : SimplePolicy Item Acc Result) (items : List (Receiver → M Item)) :
    simpleEffective policy (SimpleMethods.ofItems items) =
      simpleEffective policy { items := items } := by
  rw [SimpleMethods.ofItems_eq]
end LeanPoo.Object.MethodCombination



