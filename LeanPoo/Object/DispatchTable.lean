import LeanPoo.Object.Multimethod

/-!
The paper also describes a dispatch table as a first-class ecosystem:
generic functions, prototypes, and retroactive method declarations can be
defined independently, then assembled in one scope. The table reuses each
generic's own sparse C4 index and cache; it adds no second resolver.
-/

namespace LeanPoo.Object

/-- Each key identifies a generic function and fixes its argument, method,
and result types. Replacing a generic returns a new table. -/
structure DispatchTable (Key : Type) (Args Method Result : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  entries : Std.DHashMap Key
    (fun key => Multimethod (Args key) (Method key) (Result key))

inductive DispatchTableError (Key : Type) where
  | missing (key : Key)
  | dispatch (error : MultimethodError)
  deriving Repr

namespace DispatchTable

variable {Key : Type} {Args Method Result : Key → Type}
variable [BEq Key] [LawfulBEq Key] [Hashable Key]

def empty : DispatchTable Key Args Method Result := ⟨{}⟩

def get? (table : DispatchTable Key Args Method Result)
    (key : Key) : Option (Multimethod (Args key) (Method key) (Result key)) :=
  table.entries.get? key

/-- Install a generic independently of the prototypes and methods that will
later specialize it. Reinstallation replaces only this key's generic. -/
def install (table : DispatchTable Key Args Method Result)
    (key : Key) (generic : Multimethod (Args key) (Method key) (Result key)) :
    DispatchTable Key Args Method Result :=
  { entries := table.entries.insert key generic }

def lookup (table : DispatchTable Key Args Method Result) (key : Key) :
    Except (DispatchTableError Key)
      (Multimethod (Args key) (Method key) (Result key)) :=
  match table.get? key with
  | some generic => .ok generic
  | none => .error (.missing key)

/-- A method can be contributed by a module that owns neither the prototype
nor the generic. Only the named generic's cache is invalidated. -/
def register (table : DispatchTable Key Args Method Result)
    (key : Key) (specializers : List Specializer) (method : Method key) :
    Except (DispatchTableError Key) (DispatchTable Key Args Method Result) := do
  let generic ← table.lookup key
  let updated ← (generic.register specializers method).mapError .dispatch
  return table.install key updated

def registerWhen (table : DispatchTable Key Args Method Result)
    (key : Key) (specializers : List Specializer)
    (predicate : Args key → Bool) (method : Method key) :
    Except (DispatchTableError Key) (DispatchTable Key Args Method Result) := do
  let generic ← table.lookup key
  let updated ←
    (generic.registerWhen specializers predicate method).mapError .dispatch
  return table.install key updated

/-- A call updates the selected generic's immutable candidate cache in a
new table; other generic functions retain their entries. -/
def call (table : DispatchTable Key Args Method Result)
    (key : Key) (args : Args key) :
    Except (DispatchTableError Key)
      (Result key × DispatchTable Key Args Method Result) := do
  let generic ← table.lookup key
  let (result, updated) ← (generic.call args).mapError .dispatch
  return (result, table.install key updated)

/-- An ecosystem extension is one StateT computation. If any declaration
fails, `Except` yields no partially updated table. -/
abbrev Edit (A : Type) :=
  StateT (DispatchTable Key Args Method Result)
    (Except (DispatchTableError Key)) A

def registerIn (key : Key) (specializers : List Specializer)
    (method : Method key) : Edit (Key := Key) (Args := Args)
      (Method := Method) (Result := Result) Unit := do
  let table ← get
  match table.register key specializers method with
  | .ok updated => set updated
  | .error error => throw error

def registerWhenIn (key : Key) (specializers : List Specializer)
    (predicate : Args key → Bool) (method : Method key) :
    Edit (Key := Key) (Args := Args) (Method := Method) (Result := Result)
      Unit := do
  let table ← get
  match table.registerWhen key specializers predicate method with
  | .ok updated => set updated
  | .error error => throw error

def callIn (key : Key) (args : Args key) :
    Edit (Key := Key) (Args := Args) (Method := Method) (Result := Result)
      (Result key) := do
  let table ← get
  match table.call key args with
  | .ok (result, updated) =>
      set updated
      return result
  | .error error => throw error

end DispatchTable
end LeanPoo.Object
