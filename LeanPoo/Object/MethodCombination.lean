import LeanPoo.Prototype.SlotSpec

/-!
Typed standard method combination from POOF section 9. C4 composes each
qualified contribution as an ordinary slot specification; this module only
interprets the accumulated, most-specific-first method groups.
-/

namespace LeanPoo.Object.MethodCombination

/-- A next call retains the original receiver and may run effects. -/
abbrev SubMethod (Receiver : Type) (M : Type → Type) (Result : Type) :=
  (Unit → M Result) → Receiver → M Result

/-- Before and after methods do not receive `next`. -/
abbrev SideMethod (Receiver : Type) (M : Type → Type) :=
  Receiver → M Unit

/-- One qualifier determines the type of its method body. -/
inductive Contribution (Receiver : Type) (M : Type → Type) (Result : Type) where
  | primary (method : SubMethod Receiver M Result)
  | before (method : SideMethod Receiver M)
  | after (method : SideMethod Receiver M)
  | around (method : SubMethod Receiver M Result)

/-- C4 resolution stores methods in most-specific-first order. -/
structure Methods (Receiver : Type) (M : Type → Type) (Result : Type) where
  primary : List (SubMethod Receiver M Result) := []
  before : List (SideMethod Receiver M) := []
  after : List (SideMethod Receiver M) := []
  around : List (SubMethod Receiver M Result) := []

def Methods.prepend (methods : Methods Receiver M Result)
    (contribution : Contribution Receiver M Result) :
    Methods Receiver M Result :=
  match contribution with
  | .primary method => { methods with primary := method :: methods.primary }
  | .before method => { methods with before := method :: methods.before }
  | .after method => { methods with after := method :: methods.after }
  | .around method => { methods with around := method :: methods.around }

/-- Install several qualified contributions from one class using the ordinary
delayed C4 slot chain. Source order is retained within each qualifier. -/
def specifications {Self Receiver : Type} {M : Type → Type} {Result : Type}
    (contributions : List (Contribution Receiver M Result)) :
    Prototype.SlotSpec Self (Option (Methods Receiver M Result)) :=
  .computed fun _ inherited =>
    some (contributions.foldr (fun item methods => methods.prepend item)
      ((inherited ()).getD {}))

/-- A single qualified method is the common case of `specifications`. -/
def specification {Self Receiver : Type} {M : Type → Type} {Result : Type}
    (contribution : Contribution Receiver M Result) :
    Prototype.SlotSpec Self (Option (Methods Receiver M Result)) :=
  specifications [contribution]

/-- Each contribution is inserted ahead of its inherited group. -/
theorem specification_eval {Self Receiver : Type} {M : Type → Type}
    {Result : Type} (contribution : Contribution Receiver M Result)
    (self : Self)
    (inherited : Prototype.Next (Option (Methods Receiver M Result))) :
    (specification contribution).eval self inherited =
      some (((inherited ()).getD {}).prepend contribution) := rfl

/-- Pass `next` as a thunk that always uses the original receiver. -/
def callChain {Receiver : Type} {M : Type → Type} {Result : Type}
    (methods : List (SubMethod Receiver M Result))
    (onExhausted : Receiver → M Result) : Receiver → M Result :=
  methods.foldr (fun method next receiver =>
    method (fun _ => next receiver) receiver) onExhausted

theorem callChain_nil {Receiver : Type} {M : Type → Type}
    {Result : Type} (onExhausted : Receiver → M Result) :
    callChain ([] : List (SubMethod Receiver M Result)) onExhausted =
      onExhausted := rfl

theorem callChain_cons {Receiver : Type} {M : Type → Type}
    {Result : Type} (method : SubMethod Receiver M Result)
    (rest : List (SubMethod Receiver M Result))
    (onExhausted : Receiver → M Result) (receiver : Receiver) :
    callChain (method :: rest) onExhausted receiver =
      method (fun _ => callChain rest onExhausted receiver) receiver := rfl

/-- Around methods wrap before, primary, and after. Before methods run from
most to least specific; after methods run in the reverse order. -/
def effective {Receiver : Type} {M : Type → Type} {Result : Type}
    [Monad M] (methods : Methods Receiver M Result)
    (onMissing : Receiver → M Result) : Receiver → M Result :=
  callChain methods.around fun receiver => do
    for before in methods.before do
      before receiver
    let result ← callChain methods.primary onMissing receiver
    for after in methods.after.reverse do
      after receiver
    return result

/-- A forwarding method may pass a new payload to the remaining method
chain. `none` retains the current payload. The dispatch part of the call is
not accepted by `next`, so the resolved C4 order remains fixed. -/
abbrev ForwardMethod (Dispatch Payload : Type) (M : Type → Type)
    (Result : Type) :=
  (Option Payload → M Result) → (Dispatch × Payload) → M Result

inductive ForwardContribution (Dispatch Payload : Type)
    (M : Type → Type) (Result : Type) where
  | primary (method : ForwardMethod Dispatch Payload M Result)
  | before (method : SideMethod (Dispatch × Payload) M)
  | after (method : SideMethod (Dispatch × Payload) M)
  | around (method : ForwardMethod Dispatch Payload M Result)

structure ForwardMethods (Dispatch Payload : Type)
    (M : Type → Type) (Result : Type) where
  primary : List (ForwardMethod Dispatch Payload M Result) := []
  before : List (SideMethod (Dispatch × Payload) M) := []
  after : List (SideMethod (Dispatch × Payload) M) := []
  around : List (ForwardMethod Dispatch Payload M Result) := []

def ForwardMethods.prepend (methods : ForwardMethods Dispatch Payload M Result)
    (contribution : ForwardContribution Dispatch Payload M Result) :
    ForwardMethods Dispatch Payload M Result :=
  match contribution with
  | .primary method => { methods with primary := method :: methods.primary }
  | .before method => { methods with before := method :: methods.before }
  | .after method => { methods with after := method :: methods.after }
  | .around method => { methods with around := method :: methods.around }

/-- Each `next` closure captures the current dispatch argument, while its
optional payload replaces only the value passed to the next method. -/
def callForwardChain {Dispatch Payload : Type} {M : Type → Type}
    {Result : Type}
    (methods : List (ForwardMethod Dispatch Payload M Result))
    (onExhausted : (Dispatch × Payload) → M Result) :
    (Dispatch × Payload) → M Result :=
  methods.foldr (fun method next call =>
    method (fun replacement =>
      next (call.1, replacement.getD call.2)) call) onExhausted

theorem callForwardChain_cons {Dispatch Payload : Type} {M : Type → Type}
    {Result : Type} (method : ForwardMethod Dispatch Payload M Result)
    (rest : List (ForwardMethod Dispatch Payload M Result))
    (onExhausted : (Dispatch × Payload) → M Result)
    (call : Dispatch × Payload) :
    callForwardChain (method :: rest) onExhausted call =
      method (fun replacement =>
        callForwardChain rest onExhausted
          (call.1, replacement.getD call.2)) call := rfl

/-- The standard qualifier order with payload-forwarding `next`. An around
method may change the payload observed by the whole inner combination; a
primary method may change it for the remaining primary methods. -/
def forwardEffective {Dispatch Payload : Type} {M : Type → Type}
    {Result : Type} [Monad M]
    (methods : ForwardMethods Dispatch Payload M Result)
    (onMissing : (Dispatch × Payload) → M Result) :
    (Dispatch × Payload) → M Result :=
  callForwardChain methods.around fun call => do
    for before in methods.before do
      before call
    let result ← callForwardChain methods.primary onMissing call
    for after in methods.after.reverse do
      after call
    return result

/-- BETA-style `inner` reverses the usual next-method control: the least
specific method runs first and decides whether to enter its descendants.
An omitted `inner` stops the chain. -/
def innerChain {Receiver : Type} {M : Type → Type} {Result : Type}
    (methods : List (SubMethod Receiver M Result))
    (onInnermost : Receiver → M Result) : Receiver → M Result :=
  callChain methods.reverse onInnermost

/-- Simula inserts `inner` at the end of a body when the author omitted it.
Each body supplies a prefix and suffix; all prefixes run least-specific-first,
then all suffixes run most-specific-first. -/
structure SimulaBody (Receiver : Type) (M : Type → Type) where
  prefixPart : SideMethod Receiver M
  suffixPart : SideMethod Receiver M

def simulaEffective {Receiver : Type} {M : Type → Type} [Monad M]
    (methods : List (SimulaBody Receiver M)) : Receiver → M Unit :=
  fun receiver => do
    for method in methods.reverse do
      method.prefixPart receiver
    for method in methods do
      method.suffixPart receiver

theorem innerChain_nil {Receiver : Type} {M : Type → Type}
    {Result : Type} (onInnermost : Receiver → M Result) :
    innerChain ([] : List (SubMethod Receiver M Result)) onInnermost =
      onInnermost := rfl

/-- A simple method cannot call `next`; only an around method can wrap the
combined result. The accumulator may have a different type from either the
individual method result or the final result. -/
structure SimplePolicy (Item Acc Result : Type) where
  stop : Acc → Bool
  empty : Acc
  first : Item → Acc
  step : Item → Acc → Acc
  finish : Acc → Result

structure SimpleMethods (Receiver : Type) (M : Type → Type)
    (Item Result : Type) where
  items : List (Receiver → M Item) := []
  around : List (SubMethod Receiver M Result) := []

inductive SimpleContribution (Receiver : Type) (M : Type → Type)
    (Item Result : Type) where
  | item (method : Receiver → M Item)
  | around (method : SubMethod Receiver M Result)

def SimpleMethods.prepend (methods : SimpleMethods Receiver M Item Result)
    (contribution : SimpleContribution Receiver M Item Result) :
    SimpleMethods Receiver M Item Result :=
  match contribution with
  | .item method => { methods with items := method :: methods.items }
  | .around method => { methods with around := method :: methods.around }

/-- C4 also owns precedence for the simple method groups. -/
def simpleSpecifications {Self Receiver : Type} {M : Type → Type}
    {Item Result : Type}
    (contributions : List (SimpleContribution Receiver M Item Result)) :
    Prototype.SlotSpec Self (Option (SimpleMethods Receiver M Item Result)) :=
  .computed fun _ inherited =>
    some (contributions.foldr (fun item methods => methods.prepend item)
      ((inherited ()).getD {}))

private def foldSimple {Receiver : Type} {M : Type → Type}
    {Item Acc Result : Type} [Monad M]
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver) :
    Acc → List (Receiver → M Item) → M Acc
  | acc, [] => pure acc
  | acc, method :: rest => do
      if policy.stop acc then
        return acc
      let value ← method receiver
      foldSimple policy receiver (policy.step value acc) rest

/-- Run simple methods most-specific-first with explicit short-circuiting.
An empty group returns `policy.finish policy.empty`. -/
def simpleEffective {Receiver : Type} {M : Type → Type}
    {Item Acc Result : Type} [Monad M]
    (policy : SimplePolicy Item Acc Result)
    (methods : SimpleMethods Receiver M Item Result) : Receiver → M Result :=
  callChain methods.around fun receiver => do
    match methods.items with
    | [] => return policy.finish policy.empty
    | first :: rest =>
        let value ← first receiver
        let acc ← foldSimple policy receiver (policy.first value) rest
        return policy.finish acc

end LeanPoo.Object.MethodCombination
