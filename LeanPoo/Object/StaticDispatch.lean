import LeanPoo.Object.InlineDispatch

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
  generic : Multimethod Args Method Result
  witness : Args
  candidates : Array (MethodCandidate Args Method)
  valid : candidates = generic.candidatesFor (generic.precedence witness)
  arityValid : (generic.precedence witness).length = generic.arity

def StaticDispatch.shape (compiled : StaticDispatch Args Method Result) :
    List (List String) :=
  compiled.generic.precedence compiled.witness

/-- A caller that proves equal C4 shapes can bypass both dynamic shape
comparison and method-index traversal. Candidate predicates remain dynamic. -/
def StaticDispatch.call (compiled : StaticDispatch Args Method Result)
    (args : Args) (_sameShape : compiled.generic.precedence args = compiled.shape) :
    Result :=
  let methods := MethodCandidate.select compiled.candidates args
  compiled.generic.combine methods args

inductive StaticDispatchError where
  | shapeMismatch (expected actual : List (List String))
  deriving Repr, BEq

/-- At a dynamic boundary, check the shape before calling preselected code.
This still avoids traversing the sparse method index. -/
def StaticDispatch.callChecked (compiled : StaticDispatch Args Method Result)
    (args : Args) : Except StaticDispatchError Result :=
  if sameShape : compiled.generic.precedence args = compiled.shape then
    .ok (compiled.call args sameShape)
  else
    .error (.shapeMismatch compiled.shape (compiled.generic.precedence args))

/-- Resolve the full C4 shape once. Later registration yields a new generic;
this compiled snapshot continues to use its original candidate sequence. -/
def Multimethod.compile (generic : Multimethod Args Method Result)
    (witness : Args) :
    Except MultimethodError (StaticDispatch Args Method Result) :=
  if validArity : (generic.precedence witness).length = generic.arity then
    .ok { generic
          witness
          candidates := generic.candidatesFor (generic.precedence witness)
          valid := rfl
          arityValid := validArity }
  else
    .error (.arity generic.arity (generic.precedence witness).length)

/-- The compiled call agrees with the source generic's uncached semantic
dispatch for every argument with the witnessed C4 shape. In particular,
value-sensitive predicates are still applied to the current arguments. -/
theorem StaticDispatch.call_sound
    (compiled : StaticDispatch Args Method Result) (args : Args)
    (sameShape : compiled.generic.precedence args = compiled.shape) :
    InlineDispatch.direct compiled.generic args =
      .ok (compiled.call args sameShape) := by
  simp [InlineDispatch.direct, StaticDispatch.call, sameShape,
    StaticDispatch.shape, compiled.arityValid, compiled.valid]
  rfl

/-- A checked call on the compiled shape has the same result as the source
generic. A different shape is reported rather than silently reusing code. -/
theorem StaticDispatch.callChecked_sound
    (compiled : StaticDispatch Args Method Result) (args : Args)
    (sameShape : compiled.generic.precedence args = compiled.shape) :
    compiled.callChecked args = .ok (compiled.call args sameShape) := by
  simp [StaticDispatch.callChecked, sameShape]

theorem StaticDispatch.call_witness
    (compiled : StaticDispatch Args Method Result) :
    compiled.call compiled.witness rfl =
      compiled.generic.combine
        (compiled.candidates.foldl (fun found candidate =>
          if candidate.applies compiled.witness then
            found.push candidate.method else found) #[])
        compiled.witness := rfl

end LeanPoo.Object
