import LeanPoo.Object.DispatchTable
import LeanPoo.Object.Memo

namespace LeanPoo.Tests.DispatchTable

abbrev Payload : String → Type := fun _ => Nat
abbrev Item := Object.Plan String Payload

/-- The table key fixes the full signature of each independent generic. -/
inductive Protocol where
  | describe
  | score
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Args : Protocol → Type
  | .describe | .score => Item

abbrev Method : Protocol → Type
  | .describe => String
  | .score => Nat

abbrev Result : Protocol → Type
  | .describe => List String
  | .score => Nat

abbrev Table := Object.DispatchTable Protocol Args Method Result
abbrev Error := Object.DispatchTableError Protocol

def describe : Object.Multimethod (Args .describe)
    (Method .describe) (Result .describe) :=
  { arity := 1
    precedence := fun item => [item.precedence]
    combine := fun methods _ => methods.toList }

def score : Object.Multimethod (Args .score)
    (Method .score) (Result .score) :=
  { arity := 1
    precedence := fun item => [item.precedence]
    combine := fun methods _ => methods.foldl Nat.add 0 }

/-- The prototypes are independent of both generic signatures. -/
def item : Except C4.Error Item := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base ← LeanPoo.mix empty "Base" [] Object.Declaration.empty
  LeanPoo.extend base.schema "Child" "Base" Object.Declaration.empty

def baseTable : Except Error Table := do
  let table : Table := Object.DispatchTable.empty
  let table := (table.install .describe describe).install .score score
  let table ← table.register .describe [.prototype "Base"] "base"
  table.register .score [.prototype "Base"] 1

/-- A third module contributes methods for an existing prototype and two
unrelated generics without editing any of their definitions. -/
def extension : Object.DispatchTable.Edit (Key := Protocol)
    (Args := Args) (Method := Method) (Result := Result) Unit := do
  Object.DispatchTable.registerIn .describe [.prototype "Child"] "child"
  Object.DispatchTable.registerIn .score [.prototype "Child"] 4

def exercise : Except String
    (List String × Nat × Nat × Nat × Nat) := do
  let item ← item.mapError (fun _ => "invalid C4 graph")
  let base ← baseTable.mapError (fun _ => "invalid table")
  let (_, warm) ← (base.call .describe item).mapError
    (fun _ => "invalid description call")
  let (_, warm) ← (warm.call .score item).mapError
    (fun _ => "invalid score call")
  let oldDescribeCache := ((warm.get? .describe).getD describe).cache.size
  let (_, extended) ← (extension.run warm).mapError
    (fun _ => "invalid extension")
  let revisedCache := ((extended.get? .describe).getD describe).cache.size
  let action : Object.DispatchTable.Edit (Key := Protocol)
      (Args := Args) (Method := Method) (Result := Result)
      (List String × Nat) := do
    let labels ← Object.DispatchTable.callIn .describe item
    let value ← Object.DispatchTable.callIn .score item
    return (labels, value)
  let ((labels, value), called) ← (action.run extended).mapError
    (fun _ => "invalid table call")
  let describeCache := ((called.get? .describe).getD describe).cache.size
  let scoreCache := ((called.get? .score).getD score).cache.size
  return (labels, value, oldDescribeCache, revisedCache,
    describeCache + scoreCache)

#guard match exercise with
  | .ok (["child", "base"], 5, 1, 0, 2) => true
  | _ => false

/-- A failed second declaration exposes no partially updated ecosystem;
the original immutable table remains callable. -/
def rejected : Except String (Bool × List String) := do
  let item ← item.mapError (fun _ => "invalid C4 graph")
  let base ← baseTable.mapError (fun _ => "invalid table")
  let bad : Object.DispatchTable.Edit (Key := Protocol)
      (Args := Args) (Method := Method) (Result := Result) Unit := do
    Object.DispatchTable.registerIn .describe
      [.prototype "Child"] "temporary"
    Object.DispatchTable.registerIn .score [] 99
  let failed := match bad.run base with
    | .error (.dispatch (.arity 1 0)) => true
    | _ => false
  let (labels, _) ← (base.call .describe item).mapError
    (fun _ => "invalid description call")
  return (failed, labels)

#guard match rejected with
  | .ok (true, ["base"]) => true
  | _ => false

end LeanPoo.Tests.DispatchTable
