import LeanPoo.Object.Builder
import LeanPoo.Object.Memo

/-!
Lean-native construction for the paper's object expression. `do` builds the
direct typed specification; the existing C4 compiler and memoized evaluator
remain the only inheritance and slot semantics. No Scheme syntax is copied.
-/

namespace LeanPoo.Object

universe u v

/-- Define an object in an existing C4 graph, including multiple direct
parents. Its direct slots come from one typed Lean `do` program. -/
def defineIn {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Schema Key Value) (name : String) (supers : List String)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.mix schema name supers (Declaration.build program)
  return plan.memoize

/-- Define a root object from a typed declaration program. The result retains
both its reusable C4 plan and lazy current instance. -/
def define {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let empty : Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  defineIn empty name [] program

/-- Define a new object in the receiver's C4 family. Direct parents are
chosen by name; the new instance retains the receiver's resolution mode. -/
def Memoized.defineWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (receiver : Memoized Key Value) (name : String) (supers : List String)
    (program : Declaration.Builder Key Value PUnit) :
    Except C4.Error (Memoized Key Value) := do
  let plan ← LeanPoo.mix receiver.plan.schema name supers
    (Declaration.build program)
  return receiver.rebuild plan

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
