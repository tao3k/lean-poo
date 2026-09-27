import LeanPoo.Object.Multimethod
import LeanPoo.Object.MethodCombination
import LeanPoo.Object.PreparedMultimethod

/-!
The paper separates multiple dispatch into an accepter, a combiner, and an
invoker. `Multimethod` owns the C4 accepter and sparse method index. These
constructors use Lean's typed method-combination functions as combiners;
the complete `Args` value is passed to each method as the invoker's record.
-/

namespace LeanPoo.Object.Multimethod

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
