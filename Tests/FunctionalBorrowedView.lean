import LeanPoo.Functional.BorrowedView

namespace LeanPoo.Tests.FunctionalBorrowedView
open Functional Requirements
private def Value (_ : Nat) (_ : Nat) := Nat
private def keys : List Nat := [0,1,2,0]
private def factories : Factories Nat Value keys :=
  (fun c => c, fun c => c+1, fun c => c+2, fun c => c+99, PUnit.unit)
private def expected (c : Nat) : Results Value c keys := (c,c+1,c+2,c+99,PUnit.unit)
private def ready : Certified keys (fun c data => data = expected c) :=
  ⟨factories, fun _ => rfl⟩
private def expose (offset : Nat) : ∀ c key, Value c key → Nat :=
  fun _ _ value => Nat.add value offset
private def sum {c : Nat} : {ks : List Nat} → Results (fun (_ : Nat) (_ : Nat) => Nat) c ks → Nat
  | [], _ => 0
  | _ :: _, (head, rest) => Nat.add head (sum rest)
private def independent (c offset : Nat) (requested : List Nat) : Nat :=
  (requested.map (fun key => c+key+offset)).foldl Nat.add 0

private def check (requested : List Nat) (included : ∀ key ∈ requested, key ∈ keys)
    (offset context : Nat) (slot : ContextSlot ready) : IO (ContextSlot ready × Bool) := do
  let Public := fun c data => data = observeResults (expose offset) (projectResults (expected c) requested included)
  let derive := fun (_ : Nat) data (proof : data = expected _) =>
    congrArg (fun data => observeResults (expose offset) (projectResults data requested included)) proof
  let construct := fun (c : Nat) data (proof : Public c data) =>
    (⟨sum data, congrArg sum proof⟩ : {n : Nat // n = sum (observeResults (expose offset) (projectResults (expected c) requested included))})
  let actual := slot.consumeView requested included (expose offset) Public derive construct context
  let baseline := (ready.observeProject requested included (expose offset) Public derive).consume construct context
  unless actual.1.val == independent context offset requested && actual.1.val == baseline.val do
    throw (IO.userError "borrowed consumer differs from independent/uncached values")
  let broad := actual.2.1.read context
  unless broad.2.2 && (@BEq.beq Nat inferInstance broad.1.val.1 context) && (@BEq.beq Nat inferInstance broad.1.val.2.1 (context+1)) &&
      (@BEq.beq Nat inferInstance broad.1.val.2.2.1 (context+2)) && (@BEq.beq Nat inferInstance broad.1.val.2.2.2.1 (context+99)) do
    throw (IO.userError "view discarded or changed the broad dependencies")
  let publicRead := slot.readView requested included (expose offset) Public derive context
  unless publicRead.2.2 == actual.2.2 && sum publicRead.1.val == actual.1.val do
    throw (IO.userError "read/consume state parity failure")
  return (actual.2.1, actual.2.2)

private def run : IO Unit := do
  let mut reads := 0
  let mut hits := 0
  for trace in [[0,0,1,1,0,0], [7,7,7], [23,24,25]] do
    let mut slot := ContextSlot.empty ready
    let mut previous : Option Nat := none
    for context in trace do
      for offset in [0,10] do
        for requested in [[], [0], [2,1], [0,0], [1,2,0]] do
          if included : ∀ key ∈ requested, key ∈ keys then
            let (next, reused) ← check requested included offset context slot
            unless reused == (previous == some context) do
              throw (IO.userError "cache transition disagrees with independent policy")
            slot := next
            previous := some context
            reads := reads+1
            if reused then hits := hits+1
          else throw (IO.userError "invalid test view")
  unless reads == 120 && hits == 113 do throw (IO.userError "coverage drift")
  IO.println s!"FUNCTIONAL-BORROWED-VIEW-OK reads={reads} hits={hits} misses={reads-hits} views=5 observers=2 traces=3"
#eval run

-- The returned state remains indexed by the broad certified family.
example (slot : ContextSlot ready) (c : Nat) :
    (slot.readView [] (by simp) (expose 0) (fun _ _ => True) (fun _ _ _ => trivial) c).2 =
      (slot.read c).2 := ContextSlot.readView_state _ _ _ _ _ _ _
example (slot : ContextSlot ready) (c : Nat) :
    (slot.readView [2,1] (by simp [keys]) (expose 10)
      (fun _ _ => True) (fun _ _ _ => trivial) c).1.val =
      observeResults (expose 10) (projectResults (build ready.factories c) [2,1] (by simp [keys])) :=
  ContextSlot.readView_value _ _ _ _ _ _ _

#print axioms ContextSlot.readView_state
#print axioms ContextSlot.readView_value
#print axioms ContextSlot.consumeView_value
end LeanPoo.Tests.FunctionalBorrowedView
