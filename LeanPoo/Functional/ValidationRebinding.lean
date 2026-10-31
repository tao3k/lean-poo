import LeanPoo.Functional.ClassValidation
import LeanPoo.Prototype.RecursiveCacheSemantics

/-! Receiver-bound field validation uses the existing explicit final-self request
semantics and certified memo. The selected source generator includes inheritance
and direct assignments; these laws do not infer a C3 order, host identities,
termination of arbitrary callbacks, mutable freshness, or external effect rollback. -/
namespace LeanPoo.Functional.ValidationRebinding
open Prototype Prototype.Recursive

/-- Ordinary Type validators can be lifted without losing their original errors. -/
def checked (result : Except String Value) : Interaction Key Value Value :=
  match result with | .ok value => .value value | .error cause => .error cause

/-- Normalize each selected inherited result inside the same final-self program.
Both source computations and custom validators can request checked dependencies.
An unselected field uses Interaction.value as its identity validator. -/
def rebind (source : Prototype.Recursive.Generator Key Value)
    (validate : Key → Value → Interaction Key Value Value) : Prototype.Recursive.Generator Key Value :=
  fun key => (source key).bind (validate key)

/-- Binding validation does not intercept pending observations or source failures. -/
theorem interpret_bind (tree : Interaction Key Value Result)
    (next : Result → Interaction Key Value Other) (receiver : Key → Observation Value) :
    (tree.bind next).interpret receiver =
      match tree.interpret receiver with
      | .pending => .pending
      | .error cause => .error cause
      | .value value => (next value).interpret receiver := by
  induction tree with
  | value => rfl
  | error => rfl
  | call key continuation ih =>
    simp only [Interaction.bind, Interaction.interpret]
    cases receiver key with
    | pending => rfl
    | error cause => rfl
    | value value => exact ih value

/-- Each field step uses the rebound receiver for its inherited computation and
normalizer. It never interprets a dependency against the old source closure. -/
theorem step (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key : Key) :
    solve (rebind source validate) (depth+1) key =
      match (source key).interpret (solve (rebind source validate) depth) with
      | .pending => .pending
      | .error cause => .error cause
      | .value value => (validate key value).interpret (solve (rebind source validate) depth) := by
  exact interpret_bind (source key) (validate key) _

/-- A computed alias obtains the checked dependency before its own validator. -/
theorem dependency (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key dependency : Key) (alias : source key = .call dependency .value) :
    solve (rebind source validate) (depth+1) key =
      match solve (rebind source validate) depth dependency with
      | .pending => .pending
      | .error cause => .error cause
      | .value value => (validate key value).interpret (solve (rebind source validate) depth) := by
  rw [step, alias]
  simp only [Interaction.interpret]
  cases solve (rebind source validate) depth dependency <;> rfl

/-- An identity-typed alias shares the dependency's actual checked value. -/
theorem alias_value (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key dep : Key) (value : Value) (alias : source key = .call dep .value)
    (identity : ∀ value, validate key value = .value value)
    (found : solve (rebind source validate) depth dep = .value value) :
    solve (rebind source validate) (depth+1) key = .value value := by
  rw [dependency source validate depth key dep alias, found]
  change (validate key value).interpret (solve (rebind source validate) depth) = .value value
  rw [identity]
  rfl

/-- A failed dependency suppresses the dependent computation and its validator. -/
theorem dependency_error (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key dep : Key) (cause : String) (alias : source key = .call dep .value)
    (failed : solve (rebind source validate) depth dep = .error cause) :
    solve (rebind source validate) (depth+1) key = .error cause := by
  rw [dependency source validate depth key dep alias, failed]

/-- A literal source value reaches exactly its selected normalizer; the normalizer
itself still sees the final checked receiver for any custom dependency requests. -/
theorem direct_value (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key : Key) (value : Value) (literal : source key = .value value) :
    solve (rebind source validate) (depth+1) key =
      (validate key value).interpret (solve (rebind source validate) depth) := by
  rw [step, literal]
  rfl

/-- Errors in raw getters preserve their cause and suppress field validation. -/
theorem source_error (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (depth : Nat) (key : Key) (cause : String) (failed : source key = .error cause) :
    solve (rebind source validate) (depth+1) key = .error cause := by
  rw [step, failed]
  rfl

/-- Pure Type errors survive lifting and cannot become successful field values. -/
theorem checked_error (cause : String) (receiver : Key → Observation Value) :
    (checked (.error cause) : Interaction Key Value Value).interpret receiver = .error cause := rfl

/-- POO composition retains one final self in parent and child before the entire
selected generator is rebound. This law adds no separate inheritance algorithm. -/
theorem inherited (child : Proto (Prototype.Recursive.Generator Key Value) Parent (Prototype.Recursive.Generator Key Value))
    (parent : Proto (Prototype.Recursive.Generator Key Value) Base Parent) (base : Base)
    (validate : Key → Value → Interaction Key Value Value) :
    rebind (close (compose child parent) base) validate =
      rebind (child request (parent request base)) validate := rfl

/-- A certified memo receipt belongs to the complete rebound program and agrees
with every completed observation; an old raw-program cache is a different type. -/
theorem memo_agrees (source : Prototype.Recursive.Generator Key Value) (validate : Key → Value → Interaction Key Value Value)
    (key : Key) (receipt : Cached.Receipt (rebind source validate) (rebind source validate key))
    (depth : Nat) (known : solve (rebind source validate) depth key ≠ .pending) :
    solve (rebind source validate) depth key = receipt.result.observation := receipt.agrees depth known

/-- Receiver-bound validation still requires complete success before final
refinement; a failed rebound batch cannot expose a partly admitted object. -/
theorem batch_error (shape : Carrier → Except Error Unit) (batch : Carrier → Except Error Carrier)
    (final : Carrier → Except Error Unit) (source : Carrier) (cause : Error)
    (admitted : shape source = .ok ()) (failed : batch source = .error cause) :
    ObjectContract.validateObject shape batch final source = .error cause := by
  simp [ObjectContract.validateObject, admitted, failed, Except.bind]

end LeanPoo.Functional.ValidationRebinding
