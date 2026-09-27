import LeanPoo.Object.Multimethod

/-!
The paper distinguishes runtime dictionary lookup from code selected for a
known dispatch shape. A compiled call retains the candidates for one complete
C4 shape. Its proof-taking entry point performs neither a shape check nor a
sparse-index traversal; a checked entry point is available at dynamic edges.
Value-sensitive predicates are still evaluated for every call.
-/

namespace LeanPoo.Object

/-- The witness fixes one dispatch shape. This value is a snapshot of the
generic's method table at compilation time, not a mutable view of it. -/
structure StaticDispatch (Args Method Result : Type) where
  witness : Args
  precedence : Args → List (List String)
  candidates : Array (MethodCandidate Args Method)
  combine : Array Method → Args → Result

def StaticDispatch.shape (compiled : StaticDispatch Args Method Result) :
    List (List String) :=
  compiled.precedence compiled.witness

/-- A caller that proves equal C4 shapes can bypass both dynamic shape
comparison and method-index traversal. Candidate predicates remain dynamic. -/
def StaticDispatch.call (compiled : StaticDispatch Args Method Result)
    (args : Args) (_sameShape : compiled.precedence args = compiled.shape) :
    Result :=
  let methods := compiled.candidates.foldl (fun found candidate =>
    if candidate.applies args then found.push candidate.method else found) #[]
  compiled.combine methods args

inductive StaticDispatchError where
  | shapeMismatch (expected actual : List (List String))
  deriving Repr, BEq

/-- At a dynamic boundary, check the shape before calling preselected code.
This still avoids traversing the sparse method index. -/
def StaticDispatch.callChecked (compiled : StaticDispatch Args Method Result)
    (args : Args) : Except StaticDispatchError Result :=
  if sameShape : compiled.precedence args = compiled.shape then
    .ok (compiled.call args sameShape)
  else
    .error (.shapeMismatch compiled.shape (compiled.precedence args))

/-- Resolve the full C4 shape once. Later registration yields a new generic;
this compiled snapshot continues to use its original candidate sequence. -/
def Multimethod.compile (generic : Multimethod Args Method Result)
    (witness : Args) :
    Except MultimethodError (StaticDispatch Args Method Result) := do
  let (candidates, _) ← generic.resolve witness
  return { witness
           precedence := generic.precedence
           candidates
           combine := generic.combine }

theorem StaticDispatch.call_witness
    (compiled : StaticDispatch Args Method Result) :
    compiled.call compiled.witness rfl =
      compiled.combine
        (compiled.candidates.foldl (fun found candidate =>
          if candidate.applies compiled.witness then
            found.push candidate.method else found) #[])
        compiled.witness := rfl

end LeanPoo.Object
