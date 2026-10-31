import LeanPoo.Object.MethodCombinationSemantics

/-! Preparation through unary composition of continuation endomorphisms.
The host supplies ordinary unary composition; methods retain control of next.
These equations cover pure construction and arbitrary callback results, not
Gerbil allocation, exception representation, metadata getters or compilation. -/
namespace LeanPoo.Object.MethodCombination

/-- The extensional contract of standard unary composition, in argument order. -/
def composeContinuations {α : Type} : List (α → α) → α → α
  | [] => id
  | stage :: rest => stage ∘ composeContinuations rest

/-- Standard composition applies each builder exactly as the original fold. -/
theorem composeContinuations_foldr {α : Type} (stages : List (α → α)) (terminal : α) :
    composeContinuations stages terminal = stages.foldr (fun stage next => stage next) terminal := by
  induction stages with
  | nil => rfl
  | cons stage rest ih => simp only [composeContinuations, Function.comp_apply, List.foldr_cons, ih]

/-- Independent fragments may be prepared together without changing nesting. -/
theorem composeContinuations_append {α : Type} (outer inner : List (α → α)) :
    composeContinuations (outer ++ inner) = composeContinuations outer ∘ composeContinuations inner := by
  funext terminal
  simp only [Function.comp_apply, composeContinuations_foldr, List.foldr_append]

/-- Lift a next-method callback, preserving its original receiver on every next. -/
def methodContinuation {Receiver : Type} {M : Type → Type} {Result : Type}
    (method : SubMethod Receiver M Result) (next : Receiver → M Result) : Receiver → M Result :=
  fun receiver => method (fun _ => next receiver) receiver

/-- Preparing through standard composition preserves skipping and repeated next,
and arbitrary results (including failure); it imposes no monad laws. -/
theorem composeMethods_eq_callChain {Receiver : Type} {M : Type → Type} {Result : Type}
    (methods : List (SubMethod Receiver M Result)) (terminal : Receiver → M Result) :
    composeContinuations (methods.map methodContinuation) terminal = callChain methods terminal := by
  induction methods with
  | nil => rfl
  | cons method rest ih =>
    simp only [List.map_cons, composeContinuations, Function.comp_apply]
    rw [ih]
    rfl

/-- Lift forwarding while preserving dispatch and replacing only the payload. -/
def forwardContinuation {Dispatch Payload : Type} {M : Type → Type} {Result : Type}
    (method : ForwardMethod Dispatch Payload M Result)
    (next : (Dispatch × Payload) → M Result) : (Dispatch × Payload) → M Result :=
  fun call => method (fun replacement => next (call.1, replacement.getD call.2)) call

/-- Forwarding composition is the existing optional-payload interpreter. Host
payload validation is an additional admission boundary tested in Scheme. -/
theorem composeForward_eq_callForwardChain {Dispatch Payload : Type} {M : Type → Type} {Result : Type}
    (methods : List (ForwardMethod Dispatch Payload M Result))
    (terminal : (Dispatch × Payload) → M Result) :
    composeContinuations (methods.map forwardContinuation) terminal = callForwardChain methods terminal := by
  induction methods with
  | nil => rfl
  | cons method rest ih =>
    simp only [List.map_cons, composeContinuations, Function.comp_apply]
    rw [ih]
    rfl

/-- Lift a side callback into a continuation without feeding its result onward. -/
def sideContinuation {Receiver : Type} {M : Type → Type} [Monad M]
    (method : SideMethod Receiver M) (next : Receiver → M Unit) : Receiver → M Unit :=
  fun receiver => do method receiver; next receiver

/-- A prepared side sequence preserves short-circuiting in the supplied monad. -/
theorem composeSides_eq_runSides {Receiver : Type} {M : Type → Type} [Monad M]
    (methods : List (SideMethod Receiver M)) :
    composeContinuations (methods.map sideContinuation) (fun _ => pure ()) = runSides methods := by
  induction methods with
  | nil => rfl
  | cons method rest ih =>
    simp only [List.map_cons, composeContinuations, Function.comp_apply]
    rw [ih]
    rfl

/-- Ordered side stages may be prepared before an arbitrary terminal. Successful
stages discard their result; failure prevents selection of the following stage. -/
theorem composeParts_eq_execution {Receiver Body : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] (part : Body → SideMethod Receiver M)
    (bodies : List Body) (terminal : Receiver → M Unit) (receiver : Receiver) :
    composeContinuations (bodies.map (fun body => sideContinuation (part body))) terminal receiver =
      (do
        for body in bodies do part body receiver
        terminal receiver) := by
  induction bodies with
  | nil => simp [composeContinuations]
  | cons body rest ih => simp_all [composeContinuations, sideContinuation]

/-- Standard composition prepares the complete Simula prefix/suffix sequence.
This concerns already captured callbacks; getter order is a separate host effect. -/
theorem composeSimula_eq_effective {Receiver : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] (methods : List (SimulaBody Receiver M)) (receiver : Receiver) :
    composeContinuations
      (methods.reverse.map (fun body => sideContinuation body.prefixPart) ++
        methods.map (fun body => sideContinuation body.suffixPart))
      (fun _ => pure ()) receiver = simulaEffective methods receiver := by
  simp only [composeContinuations_append, Function.comp_apply]
  rw [composeParts_eq_execution, composeParts_eq_execution]
  simp [simulaEffective]

end LeanPoo.Object.MethodCombination
