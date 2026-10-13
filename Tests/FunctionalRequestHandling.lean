import LeanPoo.Functional.RequestHandling

namespace LeanPoo.Tests.FunctionalRequestHandling
open Functional Requirements
private def equal [BEq α] : Except String α → Except String α → Bool
  | .error a, .error b => a == b
  | .ok a, .ok b => a == b
  | _, _ => false
private abbrev Value (_ _ : Nat) := Nat
private abbrev keys : List Nat := [0,1,2]
private partial def unreachable (c : Nat) : Nat := unreachable c
private def ready : Certified (Value := Value) keys (fun c values => values.1 = c+8 ∧ values.2.1 = 2*c+1) :=
  ⟨(fun c => c+8, fun c => 2*c+1, fun c => if c == 99 then unreachable c else c+90, PUnit.unit),
    fun _ => ⟨rfl,rfl⟩⟩
private abbrev Wire := (Nat × Nat) × (Bool × String)
private abbrev Input := {wire : Wire // 0 < wire.1.2 ∧ wire.1.2 ≤ 16 ∧ wire.2.2 ≠ ""}
private def schema : Codec Input Wire String := (Codec.identity Wire String).refine
  (fun wire => 0 < wire.1.2 ∧ wire.1.2 ≤ 16 ∧ wire.2.2 ≠ "") "input"
private def context (input : Input) := input.val.1.1
private def run (input : Input) (data : Snapshot ready (context input)) : Except String (Nat × String) :=
  let quantity := input.val.1.2
  if quantity > data.val.1 then .error "capacity"
  else
    let expected := quantity * data.val.2.1
    let output := (Codec.identity Nat String).refine (fun amount => amount = expected) "output"
    (output.decode (expected + if input.val.2.1 then 1 else 0)).map fun value => (value.val,input.val.2.2)
private def fingerprint (slot : ContextSlot ready) : Option (Nat × List Nat) :=
  slot.retained.map fun ⟨c, data⟩ => (c,[data.val.1,data.val.2.1,data.val.2.2.1])
private def pack (wire : Wire) : String × (Nat × (Bool × Nat)) := (wire.2.2,(wire.1.2,(wire.2.1,wire.1.1)))
private def unpack (wire : String × (Nat × (Bool × Nat))) : Wire := ((wire.2.2.2,wire.2.1),(wire.2.2.1,wire.1))
private theorem inverse (wire : Wire) : unpack (pack wire) = wire := rfl
private def alternate := schema.represent pack unpack inverse

private def check (slot : ContextSlot ready) (wire : Wire) : IO Unit := do
  let c := wire.1.1
  let qty := wire.1.2
  let valid := qty > 0 && qty ≤ 16 && wire.2.2 != ""
  let expected : Except String (Nat × String) :=
    if !valid then .error "input" else if qty > c+8 then .error "capacity"
    else if wire.2.1 then .error "output" else .ok (qty*(2*c+1),wire.2.2)
  let expectedState := if valid then some (c,[c+8,2*c+1,c+90]) else fingerprint slot
  let marker := if valid then some ((slot.retained.map (·.1)) == some c) else none
  let actual := slot.call schema context run wire
  let represented := slot.call alternate context run (pack wire)
  unless equal actual.outcome expected && fingerprint actual.next == expectedState && actual.reused == marker &&
      equal represented.outcome expected && fingerprint represented.next == expectedState && represented.reused == marker do
    throw (IO.userError "checked request changed outcome, retained state, hit marker or representation")

#eval do
  let mut singles := 0
  let mut batches := 0
  for previous in [none,some 0,some 4] do
    let slot := match previous with
      | none => ContextSlot.empty ready
      | some c => ((ContextSlot.empty ready).read c).2.1
    for c in [0,4,7] do
      for qty in [0,1,8,9,16,17] do
        for broken in [false,true] do
          for label in ["a","","b"] do
            check slot ((c,qty),(broken,label))
            singles := singles+1
    -- Any attempted read at context 99 diverges, so admission must precede it.
    for wire in [((99,0),(true,"bad")),((99,17),(false,"bad")),((99,1),(false,""))] do
      check slot wire
      singles := singles+1
    let poison : Wire := ((99,1),(false,"later"))
    let scenarios : List (List Wire × Except String (List (Nat × String)) × Option (Nat × List Nat)) :=
      [([], .ok [], fingerprint slot),
       ([((0,1),(false,"a")),((0,2),(false,"b")),((4,3),(false,"c"))],
         .ok [(1,"a"),(2,"b"),(27,"c")],some (4,[12,9,94])),
       ([((0,1),(false,"a")),((4,2),(false,"b")),((99,0),(true,"bad")),poison],
         .error "input",some (4,[12,9,94])),
       ([((0,1),(false,"a")),((0,9),(false,"bad")),poison], .error "capacity",some (0,[8,1,90])),
       ([((0,1),(false,"a")),((4,2),(true,"bad")),poison], .error "output",some (4,[12,9,94]))]
    for scenario in scenarios do
      let (wires, expected, state) := scenario
      let (actual, next) := slot.callBatch schema context run wires
      let (represented, representedNext) := slot.callBatch alternate context run (wires.map pack)
      unless equal actual expected && equal represented expected && fingerprint next == state &&
          fingerprint representedNext == state do throw (IO.userError "batch advanced after failure or lost partial cache")
      batches := batches+1
  unless singles == 333 && batches == 15 do throw (IO.userError "request coverage drift")
  IO.println s!"FUNCTIONAL-REQUEST-HANDLING-OK singles={singles} batches={batches} layouts=2"

example : True := by
  fail_if_success have wrong : Snapshot ready 1 := ((ContextSlot.empty ready).read 0).1
  trivial

#print axioms ContextSlot.call_input_error
#print axioms ContextSlot.call_input_ok
#print axioms ContextSlot.call_outcome
#print axioms ContextSlot.call_represent
#print axioms ContextSlot.callBatch_error_iff
#print axioms ContextSlot.callBatch_represent
end LeanPoo.Tests.FunctionalRequestHandling
