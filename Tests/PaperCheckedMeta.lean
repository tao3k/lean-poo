import LeanPoo.Prototype.CheckedMetaPrototype
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperCheckedMeta
abbrev Rec := Record String (fun _ => Int)
private def slot (key : String) (value : Int) : MetaPrototype.Layer Rec :=
  Object.recordSlotGen key (fun _ _ => some value)
private unsafe def run : IO Unit := do
  let empty : Rec := Record.empty
  let origin := MetaPrototype.fromRecord ({ lookup := fun key => if key == "q" then some 7 else none } : Rec)
  let a ← IO.ofExcept (MetaPrototype.instantiateChecked "A" (MetaPrototype.make (slot "x" 1) ["O"] []) [("O",origin)] empty)
  let b ← IO.ofExcept (MetaPrototype.instantiateChecked "B" (MetaPrototype.make (slot "x" 2) ["O"] []) [("O",origin)] empty)
  let registry := [("O",origin),("A",a),("B",b)]
  let builds ← IO.mkRef (0 : Nat)
  let own : MetaPrototype.Layer Rec := fun self inherited => unsafeBaseIO do
    builds.modify (·+1)
    return (Object.recordSlotGen "y" (fun final _ =>
      some ((final.get.lookup "base").getD 0 + (final.get.lookup "x").getD 0))) self inherited
  let metadata := MetaPrototype.make own ["A","B"] []
  let prepared ← IO.ofExcept (MetaPrototype.prepareChecked "C" metadata registry)
  unless prepared.order == ["C","A","B","O"] && (← builds.get) == 0 do
    throw (IO.userError "checked preparation order or forced instance")
  for value in List.range 33 do
    let base : Rec := { lookup := fun key => if key == "base" then some (Int.ofNat value) else none }
    let built := prepared.instantiate base
    let result := built.value.get
    unless result.lookup "y" == some (Int.ofNat value+1) && result.lookup "q" == some 7 &&
        (MetaPrototype.precedence built).toOption == some prepared.order do
      throw (IO.userError "reused checked registry data or final self")
  unless (← builds.get) == 33 do throw (IO.userError "prepared instance build sharing")
  let some am := a.metadata | throw (IO.userError "missing A metadata")
  for order in [["A"],["B","O"],["A","O","O"],["A","missing","O"],["A","B","O"],["O","A"]] do
    let poisoned := { a with metadata := some (am.extend (Object.recordSlotGen .precedence (fun _ _ => some order))) }
    unless !(MetaPrototype.prepareChecked "C" metadata [("O",origin),("A",poisoned),("B",b)]).isOk do
      throw (IO.userError "poisoned parent cache admitted")
  for parents in [["missing"],["C"],["A","A"]] do
    unless !(MetaPrototype.prepareChecked "C" (MetaPrototype.make (slot "z" 3) parents []) registry).isOk do
      throw (IO.userError "invalid root graph admitted")
  let badParent := { a with metadata := some (am.extend (Object.recordSlotGen .supers (fun _ _ => some ["missing"]))) }
  unless !(MetaPrototype.prepareChecked "C" metadata [("O",origin),("A",badParent),("B",b)]).isOk &&
      !(MetaPrototype.prepareChecked "C" metadata (("A",a)::registry)).isOk do throw (IO.userError "invalid registry admitted")
  unless (← builds.get) == 33 do throw (IO.userError "refused preparation forced instance")
  -- Reclosing metadata can change self-dependent getters. Checked preparation
  -- must publish the captured function/supers together with the admitted cache.
  let dynamic := (MetaPrototype.make (slot "z" 3) ["A"] []).extend
    (DelayedProto.compose
      (Object.recordSlotGen .supers (fun self _ =>
        some (if ((self.get.lookup .precedence).getD []).isEmpty then ["A"] else ["B"])))
      (Object.recordSlotGen .function (fun self _ =>
        some (if ((self.get.lookup .precedence).getD []).isEmpty then slot "z" 3 else slot "z" 9))))
  let frozen ← IO.ofExcept (MetaPrototype.instantiateChecked "Frozen" dynamic registry empty)
  unless (MetaPrototype.supers frozen).toOption == some ["A"] &&
      (MetaPrototype.precedence frozen).toOption == some ["Frozen","A","O"] &&
      frozen.value.get.lookup "z" == some 3 do throw (IO.userError "admitted metadata snapshot changed on closure")
  IO.println "POOF-CHECKED-META-OK contexts=33 cacheRefusals=6 graphRefusals=5 prepareUnforced=true sharedPlan=true frozenMetadata=true"
#eval run
end LeanPoo.Tests.PaperCheckedMeta
