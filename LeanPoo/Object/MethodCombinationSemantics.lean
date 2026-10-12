import LeanPoo.Object.MethodCombination

/-! Appendix B's standard combination, specified by ordered recursive
execution of side methods and nested next-method wrappers. Methods retain
control of whether/how often to call next; after methods run only after a
successful primary result in the chosen monad. -/
namespace LeanPoo.Object.MethodCombination

def executeSides {Receiver : Type} {M : Type → Type} [Monad M] :
    List (SideMethod Receiver M) → Receiver → M Unit
  | [], _ => pure ()
  | method :: rest, receiver => do method receiver; executeSides rest receiver

def wrapMethods {Receiver : Type} {M : Type → Type} {Result : Type} :
    List (SubMethod Receiver M Result) → (Receiver → M Result) → Receiver → M Result
  | [], terminal, receiver => terminal receiver
  | method :: rest, terminal, receiver =>
    method (fun _ => wrapMethods rest terminal receiver) receiver

def standard {Receiver : Type} {M : Type → Type} {Result : Type} [Monad M]
    (methods : Methods Receiver M Result) (onMissing : Receiver → M Result) : Receiver → M Result :=
  wrapMethods methods.around fun receiver => do
    executeSides methods.before receiver
    let result ← wrapMethods methods.primary onMissing receiver
    executeSides methods.after.reverse receiver
    return result

theorem runSides_eq_execution {Receiver : Type} {M : Type → Type} [Monad M]
    (methods : List (SideMethod Receiver M)) (receiver : Receiver) :
    runSides methods receiver = executeSides methods receiver := by
  induction methods with
  | nil => rfl
  | cons method rest ih => simp only [runSides, List.foldr_cons, executeSides]; rw [← ih]; rfl

theorem callChain_eq_wrappers {Receiver : Type} {M : Type → Type} {Result : Type}
    (methods : List (SubMethod Receiver M Result)) (terminal : Receiver → M Result) :
    callChain methods terminal = wrapMethods methods terminal := by
  induction methods with
  | nil => rfl
  | cons method rest ih =>
    funext receiver
    simp only [callChain_cons, wrapMethods, ← ih]

theorem effective_standard {Receiver : Type} {M : Type → Type} {Result : Type} [Monad M]
    (methods : Methods Receiver M Result) (onMissing : Receiver → M Result) :
    effective methods onMissing = standard methods onMissing := by
  unfold effective standard
  rw [callChain_eq_wrappers]
  congr 1
  funext receiver
  simp only [runSides_eq_execution, callChain_eq_wrappers]

theorem callChain_append {Receiver : Type} {M : Type → Type} {Result : Type}
    (outer inner : List (SubMethod Receiver M Result)) (terminal : Receiver → M Result) :
    callChain (outer ++ inner) terminal = callChain outer (callChain inner terminal) := by
  simp [callChain, List.foldr_append]

/-- Adding more-specific fragments places them outside the inherited next
chain. The terminal and receiver are unchanged throughout the chain. -/
theorem wrappers_append {Receiver : Type} {M : Type → Type} {Result : Type}
    (outer inner : List (SubMethod Receiver M Result)) (terminal : Receiver → M Result) :
    wrapMethods (outer ++ inner) terminal = wrapMethods outer (wrapMethods inner terminal) := by
  simpa only [callChain_eq_wrappers] using callChain_append outer inner terminal

theorem runSides_append {Receiver : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (first second : List (SideMethod Receiver M)) (receiver : Receiver) :
    runSides (first ++ second) receiver = (do runSides first receiver; runSides second receiver) := by
  simp only [runSides_eq_execution]
  induction first with
  | nil => simp [executeSides]
  | cons method rest ih => simp [executeSides, ih, bind_assoc]

end LeanPoo.Object.MethodCombination
