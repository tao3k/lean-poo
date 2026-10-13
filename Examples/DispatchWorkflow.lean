import LeanPoo.Functional.DispatchHandling
import LeanPoo.Object.MultimethodCombination
import LeanPoo.C4.Linearize

namespace LeanPoo.Examples.DispatchWorkflow
open Functional Object MethodCombination

structure Request where
  express : Bool
  international : Bool
  weight : Nat
  ceiling : Nat
  shortcut : Bool := false
  defective : Bool := false
  label : String

abbrev Args := {request : Request // 0 < request.weight ∧ request.weight ≤ 8 ∧ request.label ≠ ""}
def input : Codec Args Request String :=
  (Codec.identity Request String).refine
    (fun request => 0 < request.weight ∧ request.weight ≤ 8 ∧ request.label ≠ "") "input"

structure Ledger where
  stock : Nat
  charged : Nat := 0
  events : List String := []
  deriving BEq

abbrev Action := EStateM String Ledger
abbrev Fragment := Contribution Args Action Nat
abbrev Session := DispatchSession Args Fragment Nat Ledger String

structure Receipt where
  price : Nat
  ceiling : Nat
  label : String
  bounded : 0 < price ∧ price ≤ ceiling

def admit (args : Args) (value : Nat) : Except String Receipt :=
  (((Codec.identity Nat String).refine (fun price => 0 < price ∧ price ≤ args.val.ceiling) "quote").decode value).map
    (fun checked => ⟨checked.val, args.val.ceiling, args.val.label, checked.property⟩)

theorem admit_metadata (args : Args) (value : Nat) (receipt : Receipt)
    (accepted : admit args value = .ok receipt) :
    receipt.ceiling = args.val.ceiling ∧ receipt.label = args.val.label := by
  unfold admit Codec.refine Codec.identity Except.map Except.bind at accepted
  dsimp only at accepted
  split at accepted <;> first | contradiction | (cases accepted; exact ⟨rfl, rfl⟩)

theorem input_value (wire : Request) (args : Args) (decoded : input.decode wire = .ok args) : args.val = wire := by
  unfold input Codec.refine Codec.identity Except.bind at decoded
  dsimp only at decoded
  split at decoded <;> first | contradiction | (cases decoded; rfl)

theorem call_bound (session : Session) (wire : Request) (receipt : Receipt)
    (success : (session.call input admit wire).outcome = .ok receipt) :
    receipt.price ≤ wire.ceiling ∧ receipt.label = wire.label := by
  obtain ⟨args, value, decoded, accepted⟩ := session.call_admitted input admit wire receipt success
  have metadata := admit_metadata args value receipt accepted
  have aligned := input_value wire args decoded
  exact ⟨by simpa [metadata.1, aligned] using receipt.bounded.2, by simpa [aligned] using metadata.2⟩

def mark (event : String) : Action Unit := modify fun ledger => { ledger with events := ledger.events ++ [event] }
def charge (amount : Nat) : Action Unit := modify fun ledger => { ledger with charged := ledger.charged+amount }

def compile (stock : Nat) : Except String Session := do
  let carriers : C4.Graph := { nodes := [{name := "Carrier"}, {name := "Express", parentOrders := [["Carrier"]]}] }
  let regions : C4.Graph := { nodes := [{name := "Zone"}, {name := "International", parentOrders := [["Zone"]]}] }
  let carrier ← (C4.linearizeVerified carriers "Carrier").mapError (fun _ => "carrier")
  let express ← (C4.linearizeVerified carriers "Express").mapError (fun _ => "express")
  let zone ← (C4.linearizeVerified regions "Zone").mapError (fun _ => "zone")
  let international ← (C4.linearizeVerified regions "International").mapError (fun _ => "international")
  let precedence (args : Args) :=
    [if args.val.express then express.output else carrier.output,
      if args.val.international then international.output else zone.output]
  let generic := Multimethod.standard 2 precedence (fun _ => throw "missing")
  let generic ← (generic.contribute [.any,.any] (.around (fun next args => do
    mark s!"enter:{args.val.label}"
    if args.val.shortcut then
      mark "shortcut"
      return 7
    let amount ← next ()
    mark s!"exit:{args.val.label}"
    return if args.val.defective then 0 else amount))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.any,.any] (.before (fun args => do
    mark "check-stock"
    if args.val.weight > (← get).stock then throw "stock"))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Express",.any] (.before (fun args => do
    mark "express-check"
    if args.val.weight > 4 then throw "express-weight"))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.any,.any] (.primary (fun _ args => do
    mark "base"
    let amount := 2*args.val.weight
    modify fun ledger => { ledger with stock := ledger.stock-args.val.weight }
    charge amount
    return amount))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Express",.prototype "International"] (.primary (fun next _ => do
    mark "route"
    let amount ← next ()
    charge 3
    return amount+3))).mapError (fun _ => "registration")
  let generic ← (generic.registerWhen [.prototype "Express",.prototype "International"]
    (fun args => args.val.weight ≥ 3) (.primary (fun next _ => do
      mark "bulk"
      let amount ← next ()
      charge 5
      return amount+5))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.any,.any] (.after (fun _ => mark "after-base"))).mapError (fun _ => "registration")
  let generic ← (generic.contribute [.prototype "Express",.prototype "International"]
    (.after (fun _ => mark "after-route"))).mapError (fun _ => "registration")
  return ⟨generic, { stock := stock }⟩

def wire (label : String) (weight ceiling : Nat) (shortcut defective := false) : Request :=
  ⟨true,true,weight,ceiling,shortcut,defective,label⟩

def run : IO Unit := do
  let original ← match compile 10 with
    | .error error => throw (IO.userError error)
    | .ok session => pure session
  let first := original.call input admit (wire "A" 2 40)
  unless first.outcome.toOption.map (·.price) == some 7 && first.reused == some false &&
      first.next.state.events == ["enter:A","express-check","check-stock","route","base","after-base","after-route","exit:A"] do
    throw (IO.userError "standard method order or first quote differs")
  let second := first.next.call input admit (wire "B" 3 40)
  unless second.outcome.toOption.map (·.price) == some 14 && second.reused == some true &&
      (second.next.state.events.drop first.next.state.events.length) ==
        ["enter:B","express-check","check-stock","bulk","route","base","after-base","after-route","exit:B"] do
    throw (IO.userError "cached candidates froze guard applicability or labels")
  let invalid := second.next.call input admit (wire "invalid" 0 40)
  unless invalid.next.state == second.next.state && invalid.reused == none do
    throw (IO.userError "input admission touched method state")
  let refused := invalid.next.call input admit (wire "too-heavy" 5 40)
  unless refused.next.state.stock == 5 && refused.next.state.charged == 21 && refused.reused == some true &&
      (refused.next.state.events.drop second.next.state.events.length) == ["enter:too-heavy","express-check"] do
    throw (IO.userError "method refusal lost partial trace or ran remaining phases")
  let defective := refused.next.call input admit (wire "bad-producer" 1 40 false true)
  unless defective.outcome.toOption.isNone && defective.next.state.stock == 4 && defective.next.state.charged == 26 do
    throw (IO.userError "output refusal lost the actual method state")
  let resumed := defective.next.call input admit (wire "resume" 2 40)
  unless resumed.outcome.toOption.map (·.price) == some 7 && resumed.next.state.stock == 2 && resumed.next.state.charged == 33 do
    throw (IO.userError "continued order used stale state")
  let shortcut := resumed.next.call input admit (wire "shortcut" 1 3 true)
  unless shortcut.outcome.toOption.isNone && shortcut.next.state.stock == 2 && shortcut.next.state.charged == 33 &&
      (shortcut.next.state.events.drop resumed.next.state.events.length) == ["enter:shortcut","shortcut"] do
    throw (IO.userError "around bypass skipped output admission or ran inner methods")
  let plugin ← match shortcut.next.generic.contribute [.prototype "Express",.prototype "International"]
      (.before (fun _ => mark "plugin")) with
    | .error _ => throw (IO.userError "plugin refused")
    | .ok generic => pure ({ shortcut.next with generic := generic } : Session)
  let changed := plugin.call input admit (wire "new-version" 1 40)
  let old := shortcut.next.call input admit (wire "old-version" 1 40)
  unless changed.reused == some false && old.reused == some true &&
      changed.next.state.events.contains "plugin" && !(old.next.state.events.contains "plugin") &&
      changed.outcome.toOption.map (·.price) == some 5 && old.outcome.toOption.map (·.price) == some 5 &&
      original.state.stock == 10 && original.state.events.isEmpty do
    throw (IO.userError "extension retained stale candidates or modified the original session")
  IO.println "DISPATCH-WORKFLOW-OK quote=7 guarded=14 retained-stock=4 resumed-stock=2 versions=2"

#eval run
#print axioms call_bound
#print axioms DispatchSession.call_observation
#print axioms DispatchSession.callBatch_cacheSound
end LeanPoo.Examples.DispatchWorkflow
