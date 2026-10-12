import LeanPoo.Functional.ViewRetarget

namespace LeanPoo.Tests.FunctionalViewRetarget
open Functional Requirements
private abbrev Value (_ : Nat) (_ : Nat) := Nat
private abbrev Other (_ : Nat) (_ : Nat) := Nat × (Unit → Nat)
private abbrev source : List Nat := [0,1,2,0]
private def expected (c : Nat) : Results Value c source := (c+1,c+2,c+3,c+99,PUnit.unit)
private def ready : Certified source (fun c data => data = expected c) :=
  ⟨(fun c => c+1, fun c => c+2, fun c => c+3, fun c => c+99, PUnit.unit), fun _ => rfl⟩
private partial def unreachable (_ : Unit) : Nat := unreachable ()
private def candidate : (keys : List Nat) → Factories Nat Other keys
  | [] => PUnit.unit
  | key :: rest => (fun c => (c+key+1, unreachable), candidate rest)
private def expose (_ key value : Nat) := if key == 2 then 2*value else value
private def reveal (_ key : Nat) (value : Nat × (Unit → Nat)) := if key == 2 then 2*value.1 else value.1

private theorem first (key : Nat) (member : key ∈ source) :
    factoryAt ready.factories key member = fun c => c+key+1 := by
  rcases (by simpa [source] using member : key = 0 ∨ key = 1 ∨ key = 2 ∨ key = 0) with rfl | rfl | rfl | rfl <;> rfl
private theorem compatible (keys : List Nat) (included : ∀ key ∈ keys, key ∈ source) :
    Related (fun c key a b => expose c key a = reveal c key b)
      keys (project ready.factories keys included) (candidate keys) := by
  induction keys with
  | nil => trivial
  | cons key rest ih =>
    constructor
    · intro c
      change expose c key (factoryAt ready.factories key _ c) = reveal c key (c+key+1, unreachable)
      rw [first]
      rfl
    · exact ih (fun key member => included key (by simp [member]))
private def total {c : Nat} : {keys : List Nat} → Results Value c keys → Nat
  | [], _ => 0
  | _ :: _, (first, rest) => first + total rest

private def check (keys : List Nat) (included : ∀ key ∈ keys, key ∈ source)
    (slot : ContextSlot ready) (context : Nat) : IO Unit := do
  let Public := fun c values => values = observeResults expose (projectResults (expected c) keys included)
  let derive := fun (_ : Nat) values (same : values = expected _) =>
    congrArg (fun values => observeResults expose (projectResults values keys included)) same
  let moved := slot.retargetView keys included expose reveal Public derive (candidate keys) (compatible keys included)
  let construct := fun (_ : Nat) values (_ : Public _ values) => total values
  let (result, next, hit) := moved.consume construct context
  let expectedValue := (keys.map fun key => if key == 2 then 2*(context+key+1) else context+key+1).sum
  unless result == expectedValue && hit == (slot.read context).2.2 do
    throw (IO.userError "retarget changed public values, first occurrence or hit policy")
  let (_, _, hot) := next.consume construct context
  let (fresh, _, replaced) := next.consume construct (context+1)
  let expectedFresh := (keys.map fun key => if key == 2 then 2*(context+key+2) else context+key+2).sum
  unless hot && !replaced && fresh == expectedFresh do throw (IO.userError "retarget miss did not use the new narrow family")

#eval do
  let mut cases := 0
  for previous in [none, some 0, some 3] do
    let slot := match previous with
      | none => ContextSlot.empty ready
      | some c => ((ContextSlot.empty ready).read c).2.1
    for context in [0,3,7] do
      for keys in [[],[0],[2,1],[0,0],[1,0,1],[2,2,0]] do
        if included : ∀ key ∈ keys, key ∈ source then
          check keys included slot context
          cases := cases+1
        else throw (IO.userError "invalid requested view")
  unless cases == 54 do throw (IO.userError "retarget coverage drift")
  IO.println s!"FUNCTIONAL-VIEW-RETARGET-OK cases={cases} coldWarmContexts=3 requestedViews=6"

-- Changed public observations cannot be admitted merely because hidden types fit.
private def bad : Factories Nat Other [0] := (fun c => (c+9, unreachable), PUnit.unit)
example : ¬ Related (fun c key a b => expose c key a = reveal c key b)
    [0] (project ready.factories [0] (by simp [source])) bad := by
  intro related
  have conflict := related.1 0
  change 1 = 9 at conflict
  omega

#print axioms Certified.replaceView_public
#print axioms ContextSlot.observeProject_read_reused
#print axioms ContextSlot.retargetView_reused
#print axioms ContextSlot.retargetView_consume
end LeanPoo.Tests.FunctionalViewRetarget
