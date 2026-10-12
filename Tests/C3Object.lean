import LeanPoo.Object.C3

open LeanPoo
namespace LeanPoo.Tests.C3Object

abbrev Values := fun _ : String => Int
private def declaration (name : String) : Option (Object.Declaration String Values) :=
  if name == "O" then some (Object.Declaration.empty.withDefault "x" 1)
  else if name == "A" then some (Object.Declaration.empty.withSlot "x"
    (.computed fun _ inherited => (inherited ()).map (· * 2)))
  else if name == "B" then some (Object.Declaration.empty.withSlot "x" (.constant (some 3)))
  else if name == "C" then some (Object.Declaration.empty.withSlot "z"
    (.self fun self => (self "x").map (· * 2)))
  else if name == "D" then some (Object.Declaration.empty.withSlot "x" (.constant (some 10)))
  else none

private def schema : Object.C3.Schema String Values :=
  ⟨[("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["A", "B"]),
    ("D", ["C"])], declaration⟩

private def compiled := Object.compileC3 schema "C"

private theorem paper_slots (plan : Object.C3.Plan String Values) (order : List String)
    (source : Prototype.C3.GraphDerivation plan.schema.graph plan.root order)
    (key : String) (self : Object.Self String Values) :
    plan.resolve key self =
      (Object.SlotSyntax.mk plan.schema.declaration order).resolveForward key self :=
  plan.resolve_paper order source key self

#guard (compiled.map (·.precedence)).toOption == some ["C", "A", "B", "O"]
#guard (compiled.map fun plan => plan.resolve "x" (fun _ => none)).toOption == some (some 6)
#guard (compiled.map fun plan => plan.resolve "missing" (fun _ => none)).toOption == some none

private unsafe def run : IO Unit := do
  let plan ← IO.ofExcept (compiled.mapError (fun _ => "C3 compilation failed"))
  let c := plan.instantiate
  unless c.get "x" == some 6 && c.get "z" == some 12 do
    throw (IO.userError "C3 inherited composition or final self")
  let d ← IO.ofExcept ((Object.compileC3 schema "D").mapError (fun _ => "C3 compile failed"))
  let instanceValue := d.instantiate
  unless instanceValue.get "x" == some 10 && instanceValue.get "z" == some 20 &&
      c.get "z" == some 12 do
    throw (IO.userError "final-self rebinding or retained instance")
  -- An overriding child leaves a failing inherited thunk unforced.
  let failing := Object.Declaration.empty.withSlot "x" (.thunk fun _ => panic! "forced inherited")
  let overriding := Object.Declaration.empty.withSlot "x" (.constant (some (42 : Int)))
  let program : Object.SlotSyntax String Values :=
    ⟨fun name => if name == "child" then some overriding else some failing, ["child", "parent"]⟩
  unless program.resolve "x" (fun _ => none) == some 42 do
    throw (IO.userError "override forced inherited slot")
  IO.println "POOF-C3-OBJECT-OK graphToComposition=kernel finalSelf=true inheritedLazy=true retained=true"
#eval run
#print axioms paper_slots
#print axioms Object.Plan.slotSyntax_resolve
#print axioms Object.C3.linearize_eq_reference
end LeanPoo.Tests.C3Object
