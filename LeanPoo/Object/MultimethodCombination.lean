import LeanPoo.Object.MethodCombinationSemantics
import LeanPoo.Object.Multimethod
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

end LeanPoo.Object.MethodCombination
