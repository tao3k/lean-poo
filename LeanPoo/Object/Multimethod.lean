import Std

/-!
The paper's multiple dispatch index is owned by a generic function, not by
any of its argument prototypes. Each argument contributes a C4 precedence
list. A sparse trie finds methods in lexicographic tuple order and caches the
effective sequence by the complete tuple of precedence lists.
-/

namespace LeanPoo.Object

/-- A sparse index over tuples of prototype names. The value at a node is
applicable only when the entire specialization tuple has been consumed. -/
inductive MethodIndex (Method : Type) where
  | node (value : Option Method) (children : List (String × MethodIndex Method))

namespace MethodIndex

def empty : MethodIndex Method := .node none []

def child? : List (String × MethodIndex Method) → String → Option (MethodIndex Method)
  | [], _ => none
  | (name, child) :: rest, query =>
      if name == query then some child else child? rest query

/-- Register one exact specialization tuple. Replacing a tuple retains its
first index position and leaves all other specializations intact. -/
def insert (index : MethodIndex Method) (path : List String)
    (method : Method) : MethodIndex Method :=
  match index, path with
  | .node _ children, [] => .node (some method) children
  | .node value children, name :: rest =>
      let child := (child? children name).getD empty
      let updated := child.insert rest method
      let children :=
        if children.any (fun entry => entry.1 == name) then
          children.map fun entry =>
            if entry.1 == name then (name, updated) else entry
        else children ++ [(name, updated)]
      .node value children
termination_by path.length

def lookup (index : MethodIndex Method) (path : List String) : Option Method :=
  match index, path with
  | .node value _, [] => value
  | .node _ children, name :: rest =>
      (child? children name).bind (fun child => child.lookup rest)
termination_by path.length

/-- Visit only indexed branches, in the lexicographic product of the C4
orders. Array append avoids repeated concatenation of method lists. -/
def collect (index : MethodIndex Method) (orders : List (List String))
    (found : Array Method := #[]) : Array Method :=
  match index, orders with
  | .node value _, [] =>
      match value with
      | some method => found.push method
      | none => found
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

/-- A first-class generic function owns its methods, dispatch shape,
combination policy, and immutable effective-method cache. -/
structure Multimethod (Args Method Result : Type) where
  arity : Nat
  precedence : Args → List (List String)
  combine : Array Method → Args → Result
  index : MethodIndex Method := .empty
  cache : Std.HashMap (List (List String)) (Array Method) := {}

/-- Updating the generic's method table invalidates its old effective-method
cache. Existing immutable versions of the generic remain usable. -/
def Multimethod.register (generic : Multimethod Args Method Result)
    (specializers : List String) (method : Method) :
    Except MultimethodError (Multimethod Args Method Result) :=
  if specializers.length != generic.arity then
    .error (.arity generic.arity specializers.length)
  else
    .ok { generic with
      index := generic.index.insert specializers method
      cache := {} }

/-- A cache hit reuses the effective method sequence. A miss traverses only
the sparse tuple index and returns a new generic containing that entry. -/
def Multimethod.resolve (generic : Multimethod Args Method Result)
    (args : Args) :
    Except MultimethodError (Array Method × Multimethod Args Method Result) := do
  let orders := generic.precedence args
  if orders.length != generic.arity then
    throw (.arity generic.arity orders.length)
  match generic.cache.get? orders with
  | some methods => return (methods, generic)
  | none =>
      let methods := generic.index.collect orders
      return (methods, { generic with cache := generic.cache.insert orders methods })

def Multimethod.call (generic : Multimethod Args Method Result) (args : Args) :
    Except MultimethodError (Result × Multimethod Args Method Result) := do
  let (methods, updated) ← generic.resolve args
  return (generic.combine methods args, updated)

theorem Multimethod.resolve_cached
    (generic : Multimethod Args Method Result) (args : Args)
    (methods : Array Method)
    (arity : (generic.precedence args).length = generic.arity)
    (cached : generic.cache.get? (generic.precedence args) = some methods) :
    generic.resolve args = .ok (methods, generic) := by
  have cached' : generic.cache[generic.precedence args]? = some methods := cached
  simp [Multimethod.resolve, arity, cached']
  rfl

theorem Multimethod.register_cache_empty
    (generic : Multimethod Args Method Result)
    (specializers : List String) (method : Method)
    (registered : specializers.length = generic.arity) :
    (generic.register specializers method).map (fun revised => revised.cache) =
      .ok {} := by
  simp [Multimethod.register, registered, Except.map]

end LeanPoo.Object
