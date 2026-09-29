import LeanPoo.Object.Builder
import LeanPoo.Object.Memo

/-!
Lean-native construction for the paper's object expression. `do` builds the
direct typed specification; the existing C4 compiler and memoized evaluator
remain the only inheritance and slot semantics. No Scheme syntax is copied.
-/

namespace LeanPoo.Object

universe u v

/-- Define an object with complete C4 node metadata in an existing graph.
Its direct slots come from one typed Lean `do` program. -/
def defineNodeIn {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (node : C4.Node)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.mixC4 schema node (Declaration.build program)
  return plan.memoize

/-- Define an object in an existing C4 graph with flat, ordered parents. -/
def defineIn {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (name : String) (supers : List String)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) :=
  defineNodeIn schema
    { name, parentOrders := if supers.isEmpty then [] else [supers] } program

/-- Define a root object from a typed declaration program. The result retains
both its reusable C4 plan and lazy current instance. -/
def define {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let empty : Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  defineIn empty name [] program

/-- Define a new object in the receiver's C4 family from complete node
metadata, retaining the receiver's resolution mode. -/
def Memoized.defineNodeWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (receiver : Memoized Key Value) (node : C4.Node)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.mixC4 receiver.plan.schema node (Declaration.build program)
  return receiver.rebuild plan

/-- Define a new object in the receiver's C4 family with flat, ordered
parents chosen by name. -/
def Memoized.defineWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (receiver : Memoized Key Value) (name : String) (supers : List String)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) :=
  receiver.defineNodeWith
    { name, parentOrders := if supers.isEmpty then [] else [supers] } program

/-- Define an object whose direct parents are first-class objects from
disjoint C4 families. The receiver's resolution mode is retained. -/
def Memoized.defineFrom {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (first : Memoized Key Value) (name : String)
    (others : List (Memoized Key Value))
    (program : Declaration.Builder Key Value PUnit) :
    Except CombineError (Memoized Key Value) :=
  first.mixMany others name (Declaration.build program)

/-- Define a child object with an open direct specification. The source
object and its existing lazy cells stay unchanged; the child gets a fresh
instance with final-self reads and inherited computations. -/
def Memoized.extendWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (parent : Memoized Key Value) (name : String)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) :=
  parent.defineWith name [parent.plan.root] program

end LeanPoo.Object
