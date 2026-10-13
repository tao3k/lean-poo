import LeanPoo.Functional.DispatchHandling
import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Tests.FunctionalDispatchHandling
open Functional Object MethodCombination

structure Request where
  kind : Nat
  weight : Nat
  ceiling : Nat
  bypass : Bool
  recover : Bool
  corrupt : Bool
  label : String
abbrev Args := {request : Request // 0 < request.weight ∧ request.weight ≤ 6 ∧ request.label ≠ ""}
def input : Codec Args Request String := (Codec.identity Request String).refine
  (fun request => 0 < request.weight ∧ request.weight ≤ 6 ∧ request.label ≠ "") "input"
structure Ledger where
  stock : Nat
  paid : Nat := 0
  events : List String := []
  deriving BEq
abbrev Action := EStateM String Ledger
abbrev Fragment := Contribution Args Action Nat
abbrev Session := DispatchSession Args Fragment Nat Ledger String
abbrev Approved := {pair : Nat × Nat // 0 < pair.1 ∧ pair.1 ≤ pair.2}
abbrev Failure := DispatchFailure String
def admit (args : Args) (value : Nat) : Except String Approved :=
  ((Codec.identity (Nat × Nat) String).refine (fun pair => 0 < pair.1 ∧ pair.1 ≤ pair.2) "output").decode
    (value,args.val.ceiling)
def mark (event : String) : Action Unit := modify fun ledger => { ledger with events := ledger.events++[event] }
def charge (price : Nat) : Action Unit := modify fun ledger => { ledger with paid := ledger.paid+price }
def precedence (args : Args) : List (List String) :=
  match args.val.kind with
  | 0 => [["Fast","Base"],["Zone"]]
  | 1 => [["Base"],["Zone"]]
  | 2 => [["Unknown"],["Zone"]]
  | 3 => []
  | other => [[s!"Extra{other}","Base"],["Zone"]]

def compile : Except MultimethodError (Multimethod Args Fragment (Action Nat)) := do
  let generic := Multimethod.standard 2 precedence (fun _ => do mark "missing"; throw "missing")
  let generic ← generic.contribute [.any,.any] (.around (fun next args => do
    mark s!"enter:{args.val.label}"
    if args.val.bypass then
      mark "bypass"
      return 4
    let price ← if args.val.recover then DispatchSession.recoverMethod (next ()) (fun _ => do mark "recover"; return 4) else next ()
    mark s!"exit:{args.val.label}"
    return if args.val.corrupt then 0 else price))
  let generic ← generic.contribute [.any,.any] (.before (fun args => do
    mark "check"
    if args.val.weight > (← get).stock then throw "stock"))
  let generic ← generic.contribute [.prototype "Base",.any] (.primary (fun _ args => do
    mark "base"
    modify fun ledger => { ledger with stock := ledger.stock-args.val.weight }
    charge (2*args.val.weight)
    return 2*args.val.weight))
  let generic ← generic.contribute [.prototype "Fast",.any] (.primary (fun next _ => do
    mark "fast"
    let price ← next ()
    charge 3
    return price+3))
  let generic ← generic.registerWhen [.prototype "Fast",.any] (fun args => args.val.weight ≥ 3)
    (.primary (fun next _ => do mark "bulk"; let price ← next (); charge 5; return price+5))
  let generic ← generic.contribute [.any,.any] (.after (fun _ => mark "after-general"))
  generic.contribute [.prototype "Fast",.any] (.after (fun _ => mark "after-fast"))

-- Direct branch/price/trace formulas form an independent control. This does not
-- enumerate dispatch tuples, execute method callbacks or invoke the combiner.
def control (state : Ledger) (wire : Request) : Except Failure (Nat × Nat) × Ledger := Id.run do
  if wire.weight == 0 || wire.weight > 6 || wire.label == "" then return (.error (.input "input"),state)
  if wire.kind == 3 then return (.error (.shape (.arity 2 0)),state)
  let enter := [s!"enter:{wire.label}"]
  let exit := [s!"exit:{wire.label}"]
  let fast := wire.kind == 0
  let bulk := fast && wire.weight ≥ 3
  let missing := wire.kind == 2
  let mut next := state
  let mut price := 4
  if wire.bypass then next := { state with events := state.events++enter++["bypass"] }
  else if wire.weight > state.stock || missing then
    let trace := enter++["check"]++(if wire.weight > state.stock then [] else ["missing"])
    next := {state with events := state.events++trace}
    if !wire.recover then return (.error (.method (if wire.weight > state.stock then "stock" else "missing")),next)
    next := {next with events := next.events++["recover"]++exit}
    price := if wire.corrupt then 0 else 4
  else
    price := 2*wire.weight+(if fast then 3 else 0)+(if bulk then 5 else 0)
    next := ⟨state.stock-wire.weight,state.paid+price,state.events++enter++["check"]++
      (if bulk then ["bulk"] else [])++(if fast then ["fast"] else [])++["base","after-general"]++
      (if fast then ["after-fast"] else [])++exit⟩
    if wire.corrupt then price := 0
  if price == 0 || price > wire.ceiling then return (.error (.output "output"),next)
  return (.ok (price,wire.ceiling),next)

private def equal {Value : Type} [BEq Value] : Except Failure Value → Except Failure Value → Bool
  | .ok a,.ok b => a == b
  | .error a,.error b => a == b
  | _,_ => false
def controlBatch (state : Ledger) : List Request → Except Failure (List (Nat × Nat)) × Ledger
  | [] => (.ok [],state)
  | wire :: rest =>
    let (result,next) := control state wire
    match result with
    | .error error => (.error error,next)
    | .ok output =>
      let (tail,last) := controlBatch next rest
      (tail.map (output::·),last)

def run : IO Unit := do
  let generic ← match compile with | .error _ => throw (IO.userError "compile") | .ok generic => pure generic
  let mut cases := 0
  for warm in [false,true] do
    for kind in List.range 4 do
      let warmed := if warm then
        match input.decode ⟨kind,1,20,false,false,false,"warm"⟩ with
        | .error _ => generic
        | .ok args => (generic.resolve args).toOption.map Prod.snd |>.getD generic
        else generic
      for stock in [0,2,5] do
        for weight in [0,1,3,5,7] do
          for ceiling in [0,4,10,20] do
            for flags in [(false,false,false),(true,false,false),(false,true,false),(false,false,true),(false,true,true),(true,false,true)] do
              let (bypass,recover,corrupt) : Bool × Bool × Bool := flags
              let wire : Request := ⟨kind,weight,ceiling,bypass,recover,corrupt,s!"call{cases}"⟩
              let session : Session := ⟨warmed,{stock := stock,paid := 9,events := ["prior"]}⟩
              let actual := session.call input admit wire
              let expected := control session.state wire
              let reused := if weight == 0 || weight > 6 || kind == 3 then none else some warm
              unless equal (actual.outcome.map (·.val)) expected.1 && actual.next.state == expected.2 && actual.reused == reused do
                throw (IO.userError s!"dispatch outcome/state/hit differs: {cases}")
              let pair (wire : Request) := (wire.weight,wire)
              let adapted := session.call (input.represent pair Prod.snd (fun _ => rfl)) admit (pair wire)
              unless equal (adapted.outcome.map (·.val)) expected.1 && adapted.next.state == expected.2 && adapted.reused == reused do
                throw (IO.userError "wire adapter changed dispatch result or states")
              cases := cases+1
  unless cases == 2880 do throw (IO.userError s!"dispatch coverage drift: {cases}")
  let make (kind weight ceiling : Nat) (label : String) : Request := ⟨kind,weight,ceiling,false,false,false,label⟩
  let mut batches := 0
  for stock in [1,4,9] do
    for wires in [[],[make 0 1 20 "A"],[make 0 1 20 "A",make 0 3 20 "B"],
        [make 1 1 20 "A",make 2 1 20 "missing",make 0 1 20 "skipped"],
        [make 0 1 20 "A",make 0 0 20 "input",make 1 1 20 "skipped"],
        [make 0 1 20 "A",make 3 1 20 "shape",make 1 1 20 "skipped"],
        [make 1 1 20 "A",make 0 1 2 "output",make 1 1 20 "skipped"]] do
      let session : Session := ⟨generic,{stock := stock}⟩
      let actual := session.callBatch input admit wires
      let expected := controlBatch session.state wires
      unless equal (actual.1.map (List.map (·.val))) expected.1 && actual.2.state == expected.2 do
        throw (IO.userError "batch first failure or retained method state differs")
      let resumed := actual.2.call input admit (make 1 1 20 "resume")
      let continued := control expected.2 (make 1 1 20 "resume")
      unless equal (resumed.outcome.map (·.val)) continued.1 && resumed.next.state == continued.2 do
        throw (IO.userError "dispatch continuation used stale method state")
      batches := batches+1
  -- Ten distinct valid shapes exercise the existing eight-entry LRU, then
  -- repeat the evicted first shape: method values and current labels stay fresh.
  let mut session : Session := ⟨generic,{stock := 20}⟩
  let trace : List Nat := [4,5,6,7,8,9,10,11,12,13,4]
  for entry in trace.zipIdx do
    let result := session.call input admit (make entry.1 1 20 s!"lru{entry.2}")
    unless result.reused == some false && result.outcome.toOption.map (·.val.1) == some 2 do
      throw (IO.userError "LRU eviction froze a method result or retained an evicted shape")
    session := result.next
  unless session.generic.cache.size == 8 && batches == 21 do throw (IO.userError "dispatch batch/LRU coverage drift")
  IO.println s!"FUNCTIONAL-DISPATCH-OK calls={cases} batches={batches} resumes={batches} lru={trace.length}"

#eval run

private partial def unreachable (state : Ledger) : EStateM.Result String Ledger Nat := unreachable state
private partial def predicate (args : Args) : Bool := predicate args
-- A terminal around method must not invoke divergent before/primary/default bodies.
def guardedRun : IO Unit := do
  let before : SideMethod Args Action := fun _ state => match unreachable state with
    | .ok _ next => .ok () next | .error error next => .error error next
  let raw := Multimethod.standard 2 precedence (fun _ => unreachable)
  let table ← match raw.contribute [.any,.any] (.before before) with
    | .error _ => throw (IO.userError "guard setup") | .ok value => pure value
  let table ← match table.contribute [.any,.any] (.around (fun _ _ => pure 4)) with
    | .error _ => throw (IO.userError "guard setup") | .ok value => pure value
  let session : Session := ⟨table,{stock := 2}⟩
  let valid : Request := ⟨0,1,3,false,false,false,"bypass"⟩
  let skipped := session.call input admit valid
  unless equal (skipped.outcome.map (·.val)) (.error (.output "output")) && skipped.next.state == session.state do
    throw (IO.userError "terminal around forced inner callbacks or skipped output gate")
  let divergent ← match table.registerWhen [.any,.any] predicate (.before before) with
    | .error _ => throw (IO.userError "predicate setup") | .ok value => pure value
  let watched : Session := ⟨divergent,session.state⟩
  let invalid := watched.call input admit { valid with weight := 0 }
  let malformed := ({ watched with generic := { divergent with arity := 1 } } : Session).call input admit valid
  unless equal (invalid.outcome.map (·.val)) (.error (.input "input")) && invalid.reused == none &&
      equal (malformed.outcome.map (·.val)) (.error (.shape (.arity 1 2))) && malformed.reused == none do
    throw (IO.userError "admission/shape failure forced a guarded predicate")
  let late ← match table.registerWhen [.any,.any]
      (fun args => if args.val.kind == 99 then predicate args else false) (.before before) with
    | .error _ => throw (IO.userError "suffix setup") | .ok value => pure value
  let pending : Session := ⟨late,session.state⟩
  let retained := pending.callBatch input admit
    [{ valid with ceiling := 20 },{ valid with weight := 0 },{ valid with kind := 99, ceiling := 20 }]
  unless equal (retained.1.map (List.map (·.val))) (.error (.input "input")) &&
      retained.2.generic.cache.size == 1 && retained.2.state == session.state && pending.generic.cache.size == 0 do
    throw (IO.userError "failed batch lost prefix cache, changed source or forced divergent suffix")
  let action : Action Nat := fun state => .error "first" {state with paid := state.paid+1}
  let handler (_ : String) : Action Nat := fun state => .error "second" {state with paid := state.paid+2}
  match (DispatchSession.recoverMethod action handler).run session.state with
  | .error "second" next => unless next.paid == 3 do throw (IO.userError "handler restarted old state")
  | _ => throw (IO.userError "handler refusal was lost")
  IO.println "DISPATCH-GUARDS-OK terminal=1 unforced-predicates=2 batch-suffix=1 handler-failure=1"

#eval guardedRun
#print axioms DispatchSession.call_observation
#print axioms DispatchSession.call_admitted
#print axioms DispatchSession.call_cacheSound
#print axioms DispatchSession.callBatch_error_iff
#print axioms DispatchSession.callBatch_represent
#print axioms DispatchSession.recoverMethod_error
#print axioms Validation.traverseState_invariant
end LeanPoo.Tests.FunctionalDispatchHandling
