import LeanPoo.Object.Multimethod

/-!
Section 10's per-call-site inline cache for generic functions. A cached
candidate sequence is indexed by the complete C4 tuple and carries a proof
that it came from this exact immutable generic. Method registration creates a
new site with no entry. Value predicates are evaluated on every call.
-/

namespace LeanPoo.Object

/-- A one-shape entry is tied to one immutable generic. It cannot be moved
into a site for a differently registered generic by ordinary Lean code. -/
structure InlineEntry (generic : Multimethod Args Method Result) where
  shape : List (List String)
  candidates : Array (MethodCandidate Args Method)
  valid : candidates = generic.candidatesFor shape

/-- A monomorphic call site. The generic owns semantics; this state only
remembers its most recent C4 shape. -/
structure InlineDispatch (Args Method Result : Type) where
  generic : Multimethod Args Method Result
  entry : Option (InlineEntry generic) := none

namespace InlineDispatch

def create (generic : Multimethod Args Method Result) :
    InlineDispatch Args Method Result :=
  ⟨generic, none⟩

/-- Resolve by one shape comparison on a hit, or traverse the shared sparse
index on a miss. A wrong arity has the same error as `Multimethod.resolve`. -/
def resolve (site : InlineDispatch Args Method Result) (args : Args) :
    Except MultimethodError
      (Array (MethodCandidate Args Method) ×
        InlineDispatch Args Method Result) := do
  let shape := site.generic.precedence args
  if shape.length != site.generic.arity then
    throw (.arity site.generic.arity shape.length)
  if let some entry := site.entry then
    if shape = entry.shape then
      return (entry.candidates, site)
  let candidates := site.generic.candidatesFor shape
  let entry : InlineEntry site.generic := ⟨shape, candidates, rfl⟩
  return (candidates, { site with entry := some entry })

/-- The current arguments, including value-sensitive predicates, are used
after candidate lookup. The cache never stores predicate results. -/
def call (site : InlineDispatch Args Method Result) (args : Args) :
    Except MultimethodError (Result × InlineDispatch Args Method Result) := do
  let (candidates, updated) ← site.resolve args
  return (site.generic.combine (MethodCandidate.select candidates args) args,
    updated)

/-- The uncached semantic call; it is useful as an executable reference for
the site's result without requiring the generic's own cache to be populated. -/
def direct (generic : Multimethod Args Method Result) (args : Args) :
    Except MultimethodError Result := do
  let shape := generic.precedence args
  if shape.length != generic.arity then
    throw (.arity generic.arity shape.length)
  return generic.combine
    (MethodCandidate.select (generic.candidatesFor shape) args) args

/-- Candidate selection is the same sparse-index result on both an inline
hit and a miss. This is independent of value-sensitive applicability. -/
theorem resolve_sound (site : InlineDispatch Args Method Result) (args : Args)
    (arity : (site.generic.precedence args).length = site.generic.arity) :
    (site.resolve args).map Prod.fst =
      .ok (site.generic.candidatesFor (site.generic.precedence args)) := by
  cases entry : site.entry with
  | none =>
      simp [InlineDispatch.resolve, arity, entry]
      rfl
  | some cached =>
      by_cases same : site.generic.precedence args = cached.shape
      · have cachedArity : cached.shape.length = site.generic.arity := by
          rw [← same]
          exact arity
        simp [InlineDispatch.resolve, entry, same,
          cachedArity, cached.valid]
        rfl
      · simp [InlineDispatch.resolve, arity, entry, same]
        rfl

theorem call_sound (site : InlineDispatch Args Method Result) (args : Args) :
    (site.call args).map Prod.fst =
      InlineDispatch.direct site.generic args := by
  by_cases arity : (site.generic.precedence args).length = site.generic.arity
  · have resolved := site.resolve_sound args arity
    cases h : site.resolve args with
    | error error =>
        rw [h] at resolved
        cases resolved
    | ok result =>
        cases result with
        | mk candidates updated =>
            have selected : candidates =
                site.generic.candidatesFor (site.generic.precedence args) := by
              rw [h] at resolved
              cases resolved
              rfl
            simp [InlineDispatch.call, InlineDispatch.direct,
              arity, h, selected]
            rfl
  · have failed : site.resolve args =
        .error (.arity site.generic.arity
          (site.generic.precedence args).length) := by
      simp [InlineDispatch.resolve, arity]
      rfl
    have directFailed : InlineDispatch.direct site.generic args =
        .error (.arity site.generic.arity
          (site.generic.precedence args).length) := by
      simp [InlineDispatch.direct, arity]
      rfl
    rw [directFailed]
    simp [InlineDispatch.call, failed]
    rfl

/-- Registration returns a different generic, so the dependent entry is
discarded rather than relying on a possibly colliding revision counter. -/
def register (site : InlineDispatch Args Method Result)
    (specializers : List Specializer) (method : Method) :
    Except MultimethodError (InlineDispatch Args Method Result) := do
  let generic ← site.generic.register specializers method
  return ⟨generic, none⟩

def registerWhen (site : InlineDispatch Args Method Result)
    (specializers : List Specializer) (predicate : Args → Bool)
    (method : Method) :
    Except MultimethodError (InlineDispatch Args Method Result) := do
  let generic ← site.generic.registerWhen specializers predicate method
  return ⟨generic, none⟩

theorem register_empty (site : InlineDispatch Args Method Result)
    (specializers : List Specializer) (method : Method)
    (registered : specializers.length = site.generic.arity) :
    (site.register specializers method).map (fun revised => revised.entry.isNone) =
      .ok true := by
  simp [InlineDispatch.register, Multimethod.register, registered]
  rfl

theorem registerWhen_empty (site : InlineDispatch Args Method Result)
    (specializers : List Specializer) (predicate : Args → Bool)
    (method : Method)
    (registered : specializers.length = site.generic.arity) :
    (site.registerWhen specializers predicate method).map
      (fun revised => revised.entry.isNone) = .ok true := by
  simp [InlineDispatch.registerWhen, Multimethod.registerWhen, registered]
  rfl

end InlineDispatch
end LeanPoo.Object
