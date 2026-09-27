import LeanPoo.Object.Multimethod

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
