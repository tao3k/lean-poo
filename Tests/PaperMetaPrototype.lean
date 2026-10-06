import LeanPoo.Prototype.MetaPrototype
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperMetaPrototype
abbrev Rec := Record String (fun _ => Int)
private def slot (key : String) (value : Int) : MetaPrototype.Layer Rec :=
  Object.recordSlotGen key (fun _ _ => some value)
private unsafe def run : IO Unit := do
  let empty : Rec := Record.empty
  let constants : Rec := { lookup := fun key => if key == "q" then some 7 else none }
  let origin := MetaPrototype.fromRecord constants
  unless (MetaPrototype.supers origin).toOption == some [] &&
      (MetaPrototype.precedence origin).toOption == some [] do throw (IO.userError "special base metadata")
  let a ← IO.ofExcept (MetaPrototype.instantiate "A" (MetaPrototype.make (slot "x" 1) ["O"] []) [("O",origin)] empty)
  let b ← IO.ofExcept (MetaPrototype.instantiate "B" (MetaPrototype.make (slot "x" 2) ["O"] []) [("O",origin)] empty)
  let registry := [("O",origin),("A",a),("B",b)]
  let metadata := MetaPrototype.make (slot "y" 3) ["A","B"] []
  let c ← IO.ofExcept (MetaPrototype.instantiate "C" metadata registry empty)
  unless (MetaPrototype.precedence c).toOption == some ["C","A","B","O"] &&
      (["x","y","q"].map c.value.get.lookup) == [some 1,some 3,some 7] do
    throw (IO.userError "diamond cache or base constant merge")
  let changeFunction := metadata.extend (Object.recordSlotGen .function (fun _ _ => some (slot "x" 9)))
  let changed ← IO.ofExcept (MetaPrototype.instantiate "C" changeFunction registry empty)
  unless changed.value.get.lookup "x" == some 9 && c.value.get.lookup "x" == some 1 do
    throw (IO.userError "function metadata override or retained snapshot")
  let changeSupers := metadata.extend (Object.recordSlotGen .supers (fun _ _ => some ["B","A"]))
  let reordered ← IO.ofExcept (MetaPrototype.instantiate "C" changeSupers registry empty)
  unless (MetaPrototype.precedence reordered).toOption == some ["C","B","A","O"] &&
      reordered.value.get.lookup "x" == some 2 do throw (IO.userError "supers metadata override")
  -- Cached metadata is an observable ordinary slot. Child construction consumes it.
  let some am := a.metadata | throw (IO.userError "lost parent metadata")
  let overrideCache := am.extend (Object.recordSlotGen .precedence (fun _ _ => some ["A","B","O"]))
  let cached := { a with metadata := some overrideCache }
  let child ← IO.ofExcept (MetaPrototype.instantiate "D" (MetaPrototype.make (slot "z" 4) ["A"] [])
    [("O",origin),("A",cached),("B",b)] empty)
  unless (MetaPrototype.precedence child).toOption == some ["D","A","B","O"] do throw (IO.userError "cache slot override")
  let poisoned := { a with metadata := some (am.extend
    (Object.recordSlotGen .precedence (fun _ _ => some ["A","D","O"]))) }
  unless !(MetaPrototype.instantiate "D" (MetaPrototype.make (slot "z" 4) ["A"] [])
    [("O",origin),("A",poisoned)] empty).isOk do throw (IO.userError "cyclic cached order admitted")
  for parents in [["missing"],["A","A"]] do
    unless !(MetaPrototype.instantiate "C" (MetaPrototype.make (slot "z" 4) parents []) registry empty).isOk do
      throw (IO.userError "bad supers admitted")
  unless !(MetaPrototype.instantiate "A" metadata registry empty).isOk &&
      !(MetaPrototype.instantiate "C" metadata (("A",a)::registry) empty).isOk do
    throw (IO.userError "duplicate identity admitted")
  let absent := Object.ofPrototype (fun _ inherited : Thunk (MetaPrototype.MetaRecord Rec) => inherited.get)
    (Thunk.pure Record.empty)
  unless !(MetaPrototype.instantiate "C" absent registry empty).isOk do throw (IO.userError "missing metadata admitted")
  IO.println "POOF-META-OK slotOverrides=3 diamond=true baseMerge=true retainedSnapshot=true refusals=6"
#eval run
private unsafe def paperGraph : IO Unit := do
  let graph : C3.Graph := [("O",[]),("A",["O"]),("B",["O"]),("C",["O"]),("D",["O"]),("E",["O"]),
    ("K1",["A","B","C"]),("K2",["D","B","E"]),("K3",["D","A"]),("Z",["K1","K2","K3"])]
  let mut registry : MetaPrototype.Registry Rec := []
  let mut ordinal := 0
  for (name,parents) in graph do
    let metadata := MetaPrototype.make (slot name ordinal) parents []
    let built ← IO.ofExcept (MetaPrototype.instantiate name metadata registry Record.empty)
    let order ← IO.ofExcept ((C3.linearize graph name).mapError (fun _ => "C3 oracle error"))
    unless (MetaPrototype.precedence built).toOption == some order do
      throw (IO.userError "metadata C3 cache differs from graph C3")
    for ancestor in order do
      unless (built.value.get.lookup ancestor).isSome do throw (IO.userError "missing inherited paper graph slot")
    registry := (name,built) :: registry
    ordinal := ordinal+1
  IO.println "POOF-META-GRAPH-OK originalGraphObjects=10 inheritedSlots=true cachedOrders=true"
#eval paperGraph
end LeanPoo.Tests.PaperMetaPrototype
