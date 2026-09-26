import LeanPoo.Object.Memo

/-!
The paper's direct path from pure to mutable objects: store an immutable
object in a mutable cell. Every successful update installs a fresh validated
plan and lazy instance; failed updates leave the cell untouched.
-/

namespace LeanPoo.Object

/-- Mutable identity around the pure, C4-validated object value. -/
structure Mutable (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  cell : IO.Ref (Memoized Key Value)

def Mutable.new {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) : IO (Mutable Key Value) := do
  return ⟨← IO.mkRef object⟩

/-- The persistent value currently installed in the cell. -/
def Mutable.snapshot {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) : IO (Memoized Key Value) :=
  object.cell.get

def Mutable.read {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (key : Key) : IO (Option (Value key)) := do
  return (← object.snapshot).read key

/-- Revise a prototype declaration and install its new instance on success. -/
def Mutable.reviseDeclaration {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (name : String)
    (update : Declaration Key Value → Declaration Key Value) :
    IO (Except C4.Error Unit) :=
  object.cell.modifyGet fun current =>
    match current.reviseDeclaration name update with
    | .error error => (.error error, current)
    | .ok revised => (.ok (), revised)

/-- Extend the installed object and replace the value at this identity. -/
def Mutable.extend {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (name : String)
    (declaration : Declaration Key Value) : IO (Except C4.Error Unit) :=
  object.cell.modifyGet fun current =>
    match current.extend name declaration with
    | .error error => (.error error, current)
    | .ok extended => (.ok (), extended)

private def Mutable.reviseCurrent {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value)
    (update : Declaration Key Value → Declaration Key Value) :
    IO (Except C4.Error Unit) :=
  object.cell.modifyGet fun current =>
    match current.reviseDeclaration current.plan.root update with
    | .error error => (.error error, current)
    | .ok revised => (.ok (), revised)

/-- Replace one direct value at the current C4 root. Recompilation creates
a fresh lazy instance, so slots depending on this value are recomputed when
read; snapshots taken before the update retain their prior values. -/
def Mutable.putValue {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (key : Key) (value : Value key) :
    IO (Except C4.Error Unit) :=
  object.reviseCurrent (fun declaration => declaration.withValue key value)

/-- Change a direct slot computation at the current root and replace the
installed instance only after C4 recompilation succeeds. -/
def Mutable.putSlot {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (key : Key)
    (spec : Prototype.SlotSpec (Self Key Value) (Option (Value key))) :
    IO (Except C4.Error Unit) :=
  object.reviseCurrent (fun declaration => declaration.withSlot key spec)

/-- Change a root default with the same persistent instance boundary. -/
def Mutable.putDefault {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Mutable Key Value) (key : Key) (value : Value key) :
    IO (Except C4.Error Unit) :=
  object.reviseCurrent (fun declaration => declaration.withDefault key value)

end LeanPoo.Object
