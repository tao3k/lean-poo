import Std

/-!
The paper's multiple dispatch index is owned by a generic function, not by
any of its argument prototypes. Each argument contributes a C4 precedence
list. A sparse trie finds candidates in lexicographic tuple order and caches
that sequence by the complete tuple of precedence lists. Value-sensitive
predicates are checked at every call.
-/

namespace LeanPoo.Object

/-- A method can specialize on one named prototype or match every argument.
`any` is distinct from every user-defined prototype name. -/
inductive Specializer where
  | prototype (name : String)
  | any
  deriving Repr, BEq

/-- A sparse index over tuples of specializers. The value at a node is
applicable only when the entire specialization tuple has been consumed. -/
inductive MethodIndex (Method : Type) where
  | node (values : List Method)
      (children : List (Specializer × MethodIndex Method))

namespace MethodIndex

def empty : MethodIndex Method := .node [] []

def child? : List (Specializer × MethodIndex Method) →
    Specializer → Option (MethodIndex Method)
  | [], _ => none
  | (name, child) :: rest, query =>
      if name == query then some child else child? rest query

/-- Update one exact specialization tuple while retaining every other path. -/
def alter (index : MethodIndex Method) (path : List Specializer)
    (change : List Method → List Method) : MethodIndex Method :=
  match index, path with
  | .node values children, [] => .node (change values) children
  | .node values children, name :: rest =>
      let child := (child? children name).getD empty
      let updated := child.alter rest change
      let children :=
        if children.any (fun entry => entry.1 == name) then
          children.map fun entry =>
            if entry.1 == name then (name, updated) else entry
        else children ++ [(name, updated)]
      .node values children
termination_by path.length

def insert (index : MethodIndex Method) (path : List Specializer)
    (method : Method) : MethodIndex Method :=
  index.alter path (fun _ => [method])

def prepend (index : MethodIndex Method) (path : List Specializer)
    (method : Method) : MethodIndex Method :=
  index.alter path (method :: ·)

def lookup (index : MethodIndex Method) (path : List Specializer) : List Method :=
  match index, path with
  | .node values _, [] => values
  | .node _ children, name :: rest =>
      ((child? children name).map (fun child => child.lookup rest)).getD []
termination_by path.length

/-- Visit only indexed branches, in the lexicographic product of the C4
orders. Array append avoids repeated concatenation of method lists. -/
def collect (index : MethodIndex Method) (orders : List (List Specializer))
    (found : Array Method := #[]) : Array Method :=
  match index, orders with
  | .node values _, [] =>
      values.foldl (fun current method => current.push method) found
  | .node _ children, order :: rest =>
      order.foldl (fun current name =>
        match child? children name with
        | some child => child.collect rest current
        | none => current) found
termination_by orders.length

end MethodIndex

inductive MultimethodError where
  | arity (expected actual : Nat)
  deriving Repr, BEq

/-- Value-sensitive matching is checked on every call. The cache retains
candidates, rather than freezing the result of a predicate for one argument. -/
inductive MethodCandidate (Args Method : Type) where
  | always (method : Method)
  | when (predicate : Args → Bool) (method : Method)

def MethodCandidate.applies (candidate : MethodCandidate Args Method)
    (args : Args) : Bool :=
  match candidate with
  | .always _ => true
  | .when predicate _ => predicate args

def MethodCandidate.method (candidate : MethodCandidate Args Method) :
    Method :=
  match candidate with
  | .always method | .when _ method => method

def MethodCandidate.unconditional (candidate : MethodCandidate Args Method) :
    Bool :=
  match candidate with
  | .always _ => true
  | .when _ _ => false

def MethodCandidate.select (candidates : Array (MethodCandidate Args Method))
    (args : Args) : Array Method :=
  candidates.foldl (fun found candidate =>
    if candidate.applies args then found.push candidate.method else found) #[]

/-- A first-class generic function owns its methods, dispatch shape,
combination policy, and immutable candidate-sequence cache. -/
structure Multimethod (Args Method Result : Type) where
  arity : Nat
  precedence : Args → List (List String)
  combine : Array Method → Args → Result
  index : MethodIndex (MethodCandidate Args Method) := .empty
  cache : Std.HashMap (List (List String))
    (Array (MethodCandidate Args Method)) := {}

/-- Updating the generic's method table invalidates its old candidate-sequence
cache. Existing immutable versions of the generic remain usable. -/
def Multimethod.register (generic : Multimethod Args Method Result)
    (specializers : List Specializer) (method : Method) :
    Except MultimethodError (Multimethod Args Method Result) :=
  if specializers.length != generic.arity then
    .error (.arity generic.arity specializers.length)
  else
    .ok { generic with
      index := generic.index.insert specializers (.always method)
      cache := {} }

/-- Refine one specialization tuple with an equality or arbitrary predicate.
Guarded methods precede its unconditional method. Candidate matching remains
dynamic even when the C4-shaped index lookup is cached. -/
def Multimethod.registerWhen (generic : Multimethod Args Method Result)
    (specializers : List Specializer) (predicate : Args → Bool)
    (method : Method) :
    Except MultimethodError (Multimethod Args Method Result) :=
  if specializers.length != generic.arity then
    .error (.arity generic.arity specializers.length)
  else
    .ok { generic with
      index := generic.index.prepend specializers (.when predicate method)
      cache := {} }

/-- The uncached candidate sequence for one complete C4 call shape. The
generic's cache and call-site caches both use this one sparse-index traversal. -/
def Multimethod.candidatesFor (generic : Multimethod Args Method Result)
    (shape : List (List String)) : Array (MethodCandidate Args Method) :=
  generic.index.collect (shape.map fun order =>
    order.map Specializer.prototype ++ [.any])

/-- A cache hit reuses the candidate sequence. A miss traverses only
the sparse tuple index and returns a new generic containing that entry. -/
def Multimethod.resolve (generic : Multimethod Args Method Result)
    (args : Args) :
    Except MultimethodError
      (Array (MethodCandidate Args Method) × Multimethod Args Method Result) := do
  let precedence := generic.precedence args
  if precedence.length != generic.arity then
    throw (.arity generic.arity precedence.length)
  match generic.cache.get? precedence with
  | some methods => return (methods, generic)
  | none =>
      let methods := generic.candidatesFor precedence
      return (methods, { generic with
        cache := generic.cache.insert precedence methods })

def Multimethod.call (generic : Multimethod Args Method Result) (args : Args) :
    Except MultimethodError (Result × Multimethod Args Method Result) := do
  let (candidates, updated) ← generic.resolve args
  let methods := MethodCandidate.select candidates args
  return (generic.combine methods args, updated)

theorem Multimethod.resolve_cached
    (generic : Multimethod Args Method Result) (args : Args)
    (methods : Array (MethodCandidate Args Method))
    (arity : (generic.precedence args).length = generic.arity)
    (cached : generic.cache.get? (generic.precedence args) = some methods) :
    generic.resolve args = .ok (methods, generic) := by
  have cached' : generic.cache[generic.precedence args]? = some methods := cached
  simp [Multimethod.resolve, arity, cached']
  rfl

theorem Multimethod.register_cache_empty
    (generic : Multimethod Args Method Result)
    (specializers : List Specializer) (method : Method)
    (registered : specializers.length = generic.arity) :
    (generic.register specializers method).map (fun revised => revised.cache) =
      .ok {} := by
  simp [Multimethod.register, registered, Except.map]

theorem Multimethod.registerWhen_cache_empty
    (generic : Multimethod Args Method Result)
    (specializers : List Specializer)
    (predicate : Args → Bool) (method : Method)
    (registered : specializers.length = generic.arity) :
    (generic.registerWhen specializers predicate method).map
        (fun revised => revised.cache) = .ok {} := by
  simp [Multimethod.registerWhen, registered, Except.map]

theorem Multimethod.call_cached
    (generic : Multimethod Args Method Result) (args : Args)
    (candidates : Array (MethodCandidate Args Method))
    (arity : (generic.precedence args).length = generic.arity)
    (cached : generic.cache.get? (generic.precedence args) = some candidates) :
    generic.call args = .ok
      (generic.combine
        (candidates.foldl (fun found candidate =>
          if candidate.applies args then found.push candidate.method else found) #[])
        args, generic) := by
  simp [Multimethod.call, generic.resolve_cached args candidates arity cached]
  rfl

end LeanPoo.Object
